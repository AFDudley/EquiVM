import Benchmarks.EAS.EAS.Storage
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- GENERALIZES Reasoning.PackedStorage.storageLocStore_uint48_offset0_word: any byte-aligned unsigned width.
def setLowWord (old data : UInt256) (bits : Nat) : UInt256 :=
  UInt256.lor (UInt256.land (UInt256.ofNat (2^256 - 2^bits)) old)
    (UInt256.land data (UInt256.ofNat (2^bits-1)))

-- LIBRARY CANDIDATE: normalize operand order in a packed low-field update.
theorem setLowWord_eq (old data : UInt256) (bits : Nat) :
    setLowWord old data bits = UInt256.lor (UInt256.land old (UInt256.ofNat (2^256 - 2^bits)))
      (UInt256.land data (UInt256.ofNat (2^bits-1))) := by
  unfold setLowWord
  rw [u256_land_comm (UInt256.ofNat (2^256-2^bits))]

theorem storageLocStore_uint_offset0_word (evm : EVM.State) (slot data : UInt256)
    (size : Fin 33) (width : ABI.BitWidth) (hwidth : width.val = 8 * size.val)
    (hbound : 0 + size.val - 1 < 32) :
    storageLocStore evm {slot := slot, offset := 0, size := size, hbound := hbound, type := .int (.uint width)}
      (.int (Int.ofNat data.toNat)) =
      some (EVM.storageStore evm evm.executionEnv.codeOwner slot
        (setLowWord (EVM.storageLoad evm evm.executionEnv.codeOwner slot) data width.val)) := by
  unfold storageLocStore storageLocWriteWord
  simp only [valueToWord, wordOfInt_ofNat_toNat, bind, Option.bind]
  congr 2
  apply u256_inj
  change fromBytes' ((EVM.Word.toBytesLEWithSizeProof (EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.take (0 : Fin 32).val ++
    ((EVM.Word.toBytesLEWithSizeProof data).1.take size.val) ++
    (EVM.Word.toBytesLEWithSizeProof (EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.drop ((0 : Fin 32).val + size.val)) = _
  simp only [show (0 : Fin 32).val = 0 from rfl, List.take_zero, List.nil_append, Nat.zero_add]
  rw [fromBytes'_append, fromBytes'_take_wordLE, fromBytes'_drop_wordLE,
    List.length_take, (EVM.Word.toBytesLEWithSizeProof data).2, Nat.min_eq_left (by omega)]
  have hp : (256 : Nat)^size.val = 2^width.val := by
    rw [hwidth, show (256 : Nat) = 2^8 from rfl, Nat.pow_mul]
  have hl : 2^width.val - 1 < UInt256.size := by
    have hb : (2 : Nat)^width.val ≤ 2^256 := Nat.pow_le_pow_right (by decide) width.property.2.1
    have hp : 0 < (2 : Nat)^width.val := by positivity
    change 2^width.val - 1 < 2^256
    omega
  have hs : data.toNat % 2^width.val < UInt256.size :=
    lt_of_le_of_lt (Nat.mod_le _ _) (show data.toNat < UInt256.size from data.val.isLt)
  rw [hp, setLowWord, u256_lor_toNat_exact,
    u256_land_high_mask_toNat _ width.val width.property.2.1,
    u256_land_toNat, ulit_toNat' _ hl, nat_land_mask_eq_mod, Nat.mod_eq_of_lt hs, ← hwidth]
  change _ = Nat.lor (_ / 2^width.val * 2^width.val) (data.toNat % 2^width.val)
  rw [nat_lor_comm, nat_lor_shift_add _ _ width.val (Nat.mod_lt _ (by positivity))]
  rw [Nat.mul_comm]

end Benchmarks.EAS.EAS
