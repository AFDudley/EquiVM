import Benchmarks.EAS.EAS.PackedShift
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- GENERALIZES Reasoning.PackedStorage's fixed-width setters to arbitrary bit windows.
def packedSliceWord (old data : UInt256) (start width : Nat) : UInt256 :=
  UInt256.lor
    (UInt256.land old (UInt256.ofNat (Nat.lor (2^start-1) (2^256-2^(start+width)))))
    (UInt256.land (UInt256.shiftLeft data (UInt256.ofNat start))
      (UInt256.ofNat ((2^width-1)*2^start)))

theorem shiftedMask_lt (start width : Nat) (h : start+width ≤ 256) :
    (2^width-1)*2^start < UInt256.size := by
  have hp : 0 < (2 : Nat)^width := by positivity
  calc
    (2^width-1)*2^start < 2^width*2^start := Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
    _ = 2^(start+width) := by rw [← Nat.pow_add,Nat.add_comm]
    _ ≤ 2^256 := Nat.pow_le_pow_right (by decide) h

theorem packedClearMask_lt (start width : Nat) (h : start+width ≤ 256) :
    Nat.lor (2^start-1) (2^256-2^(start+width)) < UInt256.size := by
  change (2^start-1) ||| (2^256-2^(start+width)) < 2^256
  apply Nat.or_lt_two_pow
  · have hp : 0 < (2 : Nat)^start := by positivity
    have hb : (2 : Nat)^start ≤ 2^256 := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · have hp : 0 < (2 : Nat)^(start+width) := by positivity
    omega

theorem shiftLeft_maskSlice_toNat (data : UInt256) (start width : Nat)
    (hs : start < 256) (h : start+width ≤ 256) :
    (UInt256.land (UInt256.shiftLeft data (UInt256.ofNat start))
      (UInt256.ofNat ((2^width-1)*2^start))).toNat = data.toNat % 2^width * 2^start := by
  rw [uland_toNat,shiftLeft_toNat_mod _ _ hs,ulit_toNat' _ (shiftedMask_lt _ _ h)]
  rw [← Nat.shiftLeft_eq,← Nat.shiftLeft_eq,← Nat.shiftLeft_and_distrib,Nat.shiftLeft_eq]
  change Nat.land (data.toNat % 2^(256-start)) (2^width-1) * 2^start = _
  rw [nat_land_mask_eq_mod,Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

theorem packedSliceWord_toNat (old data : UInt256) (start width : Nat)
    (hs : start < 256) (h : start+width ≤ 256) :
    (packedSliceWord old data start width).toNat =
      old.toNat % 2^start + data.toNat % 2^width * 2^start + old.toNat / 2^(start+width)*2^(start+width) := by
  rw [packedSliceWord,u256_lor_toNat_exact,shiftLeft_maskSlice_toNat _ _ _ hs h,
    uland_toNat,ulit_toNat' _ (packedClearMask_lt _ _ h)]
  change Nat.lor (Nat.land old.toNat (Nat.lor (2^start-1) (2^256-2^(start+width)))) _ = _
  rw [show Nat.land old.toNat (Nat.lor (2^start-1) (2^256-2^(start+width))) =
    Nat.lor (Nat.land old.toNat (2^start-1)) (Nat.land old.toNat (2^256-2^(start+width))) from Nat.and_or_distrib_left _ _ _]
  rw [nat_land_mask_eq_mod,natLandClearLow old.toNat (start+width) h (by exact old.val.isLt)]
  let low := old.toNat % 2^start
  let mid := data.toNat % 2^width
  let high := old.toNat / 2^(start+width)
  change Nat.lor (Nat.lor low (high*2^(start+width))) (mid*2^start) = low+mid*2^start+high*2^(start+width)
  have hl : low < 2^start := Nat.mod_lt _ (by positivity)
  have hm : mid < 2^width := Nat.mod_lt _ (by positivity)
  have hm' : mid*2^start < 2^(start+width) := by
    calc
      mid*2^start < 2^width*2^start := Nat.mul_lt_mul_of_pos_right hm (by positivity)
      _ = 2^(start+width) := by rw [← Nat.pow_add,Nat.add_comm]
  rw [show Nat.lor (Nat.lor low (high*2^(start+width))) (mid*2^start) =
    Nat.lor low (Nat.lor (high*2^(start+width)) (mid*2^start)) from Nat.lor_assoc _ _ _,
    nat_lor_comm (high*2^(start+width)),nat_lor_shift_add _ _ _ hm']
  rw [show mid*2^start+high*2^(start+width) = (mid+high*2^width)*2^start by rw [Nat.pow_add]; ring]
  rw [nat_lor_shift_add _ _ _ hl,Nat.pow_add]
  ring

-- GENERALIZES Reasoning.Storage.storageLocStore_uint8 and packed setters to any byte-aligned scalar.
theorem storageLocStore_packedSlice (evm : EVM.State) (loc : StorageLoc) (value : Value) (word : UInt256)
    (hbits : loc.bitOffset = none) (hvalue : valueToWord value = some word) :
    storageLocStore evm loc value = some (EVM.storageStore evm evm.executionEnv.codeOwner loc.slot
      (packedSliceWord (EVM.storageLoad evm evm.executionEnv.codeOwner loc.slot) word (8*loc.offset.val) (8*loc.size.val))) := by
  have hoff : loc.offset.val < 32 := loc.offset.isLt
  have hsize : loc.size.val ≤ 32 := by have h := loc.size.isLt; omega
  have hsum : loc.offset.val+loc.size.val ≤ 32 := by have h := loc.hbound; omega
  unfold storageLocStore storageLocWriteWord
  simp only [hbits,hvalue,bind,Option.bind]
  congr 2
  apply u256_inj
  change fromBytes' ((EVM.Word.toBytesLEWithSizeProof (EVM.storageLoad evm evm.executionEnv.codeOwner loc.slot)).1.take loc.offset.val ++
      (EVM.Word.toBytesLEWithSizeProof word).1.take loc.size.val ++
      (EVM.Word.toBytesLEWithSizeProof (EVM.storageLoad evm evm.executionEnv.codeOwner loc.slot)).1.drop (loc.offset.val+loc.size.val)) = _
  rw [fromBytes'_append,fromBytes'_append,fromBytes'_take_wordLE,fromBytes'_take_wordLE,fromBytes'_drop_wordLE]
  simp only [List.length_append,List.length_take,(EVM.Word.toBytesLEWithSizeProof _).2,
    Nat.min_eq_left (Nat.le_of_lt hoff),Nat.min_eq_left hsize]
  rw [packedSliceWord_toNat _ _ _ _ (by omega) (by omega)]
  have hp (n : Nat) : (256 : Nat)^n = 2^(8*n) := by rw [show (256 : Nat) = 2^8 from rfl,Nat.pow_mul]
  rw [hp loc.offset.val,hp loc.size.val,hp (loc.offset.val+loc.size.val),Nat.mul_add]
  ring

end Benchmarks.EAS.EAS
