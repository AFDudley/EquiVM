import Benchmarks.EAS.EAS.PackedSlice
import Benchmarks.EAS.EAS.LowPacked
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: full-word and low-field specializations of the generic packed write.
theorem packedSliceWord_full (old data : UInt256) : packedSliceWord old data 0 256 = data := by
  apply u256_inj
  rw [packedSliceWord_toNat _ _ _ _ (by decide) (by decide)]
  simp only [Nat.pow_zero,Nat.mod_one,Nat.zero_add,Nat.mul_one,
    Nat.mod_eq_of_lt (show data.toNat < 2^256 from data.val.isLt),
    Nat.div_eq_of_lt (show old.toNat < 2^256 from old.val.isLt),Nat.zero_mul,Nat.add_zero]

theorem packedSliceWord_low (old data : UInt256) (width : Nat) :
    packedSliceWord old data 0 width = setLowWord old data width := by
  unfold packedSliceWord setLowWord
  have hs : UInt256.shiftLeft data (UInt256.ofNat 0) = data := by
    apply u256_inj
    rw [shiftLeft_toNat_mod _ _ (by decide)]
    simp only [Nat.sub_zero,Nat.pow_zero,Nat.mul_one,
      Nat.mod_eq_of_lt (show data.toNat < 2^256 from data.val.isLt)]
  simp only [Nat.pow_zero,Nat.sub_self,Nat.zero_add,Nat.mul_one,hs,
    show ∀ n, Nat.lor 0 n = n from fun n => Nat.zero_or n,u256_land_comm]

-- LIBRARY CANDIDATE: only the low field-width input bits affect a packed store.
theorem packedSliceWord_clean (old data : UInt256) (start width : Nat)
    (hs : start < 256) (h : start+width ≤ 256) :
    packedSliceWord old (UInt256.land data (UInt256.ofNat (2^width-1))) start width =
      packedSliceWord old data start width := by
  apply u256_inj
  rw [packedSliceWord_toNat _ _ _ _ hs h,packedSliceWord_toNat _ _ _ _ hs h,uland_toNat]
  have hm : 2^width-1 < UInt256.size := by
    have hp : 0 < (2 : Nat)^width := by positivity
    have hb : (2 : Nat)^width ≤ 2^256 := Nat.pow_le_pow_right (by decide) (by omega)
    change 2^width-1 < 2^256
    omega
  rw [ulit_toNat' _ hm]
  change _ + (Nat.land data.toNat (2^width-1)) % 2^width * 2^start + _ = _
  rw [nat_land_mask_eq_mod,Nat.mod_mod]

end Benchmarks.EAS.EAS
