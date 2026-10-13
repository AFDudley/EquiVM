import Benchmarks.EAS.EAS.PackedNormalize
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: combine adjacent packed stores without assumptions about slot hashes.
theorem packedSliceWord_low_mod_div (old data : UInt256) (width : Nat) (h : width ≤ 256) :
    (packedSliceWord old data 0 width).toNat % 2^width = data.toNat % 2^width ∧
    (packedSliceWord old data 0 width).toNat / 2^width = old.toNat / 2^width := by
  rw [packedSliceWord_toNat _ _ _ _ (by decide) (by omega)]
  simp only [Nat.pow_zero,Nat.mod_one,Nat.zero_add,Nat.mul_one]
  rw [Nat.add_mul_mod_self_right,Nat.mod_mod,Nat.add_mul_div_right _ _ (by positivity),
    Nat.div_eq_of_lt (Nat.mod_lt _ (by positivity)),Nat.zero_add]
  exact ⟨rfl,rfl⟩

theorem packedSliceWord_adjacent_toNat (old lo hi : UInt256) (start width : Nat)
    (hs : start < 256) (h : start+width ≤ 256) :
    (packedSliceWord (packedSliceWord old lo 0 start) hi start width).toNat =
      lo.toNat % 2^start + hi.toNat % 2^width * 2^start + old.toNat / 2^(start+width)*2^(start+width) := by
  have hp := packedSliceWord_low_mod_div old lo start (by omega)
  rw [packedSliceWord_toNat _ _ _ _ hs h,hp.1]
  have hdiv : (packedSliceWord old lo 0 start).toNat / 2^(start+width) = old.toNat / 2^(start+width) := by
    rw [Nat.pow_add,← Nat.div_div_eq_div_mul,← Nat.div_div_eq_div_mul,hp.2]
  rw [hdiv]

def adjacentPackedWord (old lo hi : UInt256) (start width : Nat) : UInt256 :=
  UInt256.lor
    (UInt256.land (UInt256.shiftLeft hi (UInt256.ofNat start)) (UInt256.ofNat ((2^width-1)*2^start)))
    (UInt256.lor (UInt256.land lo (UInt256.ofNat (2^start-1)))
      (UInt256.land old (UInt256.ofNat (2^256-2^(start+width)))))

theorem packedSliceWord_adjacent (old lo hi : UInt256) (start width : Nat)
    (hs : start < 256) (h : start+width ≤ 256) :
    packedSliceWord (packedSliceWord old lo 0 start) hi start width = adjacentPackedWord old lo hi start width := by
  apply u256_inj
  rw [packedSliceWord_adjacent_toNat _ _ _ _ _ hs h,adjacentPackedWord,u256_lor_toNat_exact,
    shiftLeft_maskSlice_toNat _ _ _ hs h,u256_lor_toNat_exact,
    u256_land_comm old (UInt256.ofNat (2^256-2^(start+width))),
    u256_land_high_mask_toNat _ (start+width) h,uland_toNat]
  have hm : 2^start-1 < UInt256.size := by
    have hp : 0 < (2 : Nat)^start := by positivity
    have hb : (2 : Nat)^start ≤ 2^256 := Nat.pow_le_pow_right (by decide) (by omega)
    change 2^start-1 < 2^256
    omega
  rw [ulit_toNat' _ hm]
  change _ = Nat.lor _ (Nat.lor (Nat.land lo.toNat (2^start-1)) _)
  rw [nat_land_mask_eq_mod,nat_lor_comm (hi.toNat % 2^width * 2^start)]
  rw [show Nat.lor (Nat.lor (lo.toNat % 2^start) (old.toNat / 2^(start+width)*2^(start+width)))
      (hi.toNat % 2^width * 2^start) = Nat.lor (lo.toNat % 2^start)
      (Nat.lor (old.toNat / 2^(start+width)*2^(start+width)) (hi.toNat % 2^width * 2^start)) from Nat.lor_assoc _ _ _]
  rw [nat_lor_comm (old.toNat / 2^(start+width)*2^(start+width))]
  have hmid : hi.toNat % 2^width * 2^start < 2^(start+width) := by
    calc
      hi.toNat % 2^width * 2^start < 2^width*2^start :=
        Nat.mul_lt_mul_of_pos_right (Nat.mod_lt _ (by positivity)) (by positivity)
      _ = 2^(start+width) := by rw [← Nat.pow_add,Nat.add_comm]
  rw [nat_lor_shift_add _ _ _ hmid]
  rw [show hi.toNat % 2^width * 2^start + old.toNat / 2^(start+width)*2^(start+width) =
      (hi.toNat % 2^width + old.toNat / 2^(start+width)*2^width)*2^start by rw [Nat.pow_add]; ring]
  rw [nat_lor_shift_add _ _ _ (Nat.mod_lt _ (by positivity)),Nat.pow_add]
  ring

theorem sstoreAdjacentPacked (σ : AccountMap) (ee : ExecutionEnv) (slot lo hi : UInt256) (start width : Nat)
    (hs : start < 256) (h : start+width ≤ 256) :
    let first := sstoreAccountMap ee.codeOwner σ slot (packedSliceWord (solcSlotWord σ ee slot) lo 0 start)
    sstoreAccountMap ee.codeOwner first slot (packedSliceWord (solcSlotWord first ee slot) hi start width) =
      sstoreAccountMap ee.codeOwner σ slot (adjacentPackedWord (solcSlotWord σ ee slot) lo hi start width) := by
  dsimp only
  cases ha : σ.get? ee.codeOwner with
  | none => simp only [sstoreAccountMap_absent_same ha]
  | some acc =>
    rw [solcSlotWord_sstore_present σ ee ha,packedSliceWord_adjacent _ _ _ _ _ hs h,
      ← sstoreAccountMap_self_update]

end Benchmarks.EAS.EAS
