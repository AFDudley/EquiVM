import Benchmarks.CurveVault.Common

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: a right shift below the word width is natural division.
theorem u256_shiftRight_toNat_of_lt (w : UInt256) (bits : Nat) (hbits : bits < 256) :
    (UInt256.shiftRight w (UInt256.ofNat bits)).toNat = w.toNat / 2 ^ bits := by
  unfold UInt256.shiftRight UInt256.toNat
  rw [if_neg]
  · change (w.val >>> (UInt256.ofNat bits).val).val = w.val.val / 2 ^ bits
    rw [Fin.shiftRight_val, Nat.shiftRight_eq_div_pow]
    have hb : bits < UInt256.size := lt_trans hbits (by decide +kernel)
    change w.val.val / 2 ^ (UInt256.ofNat bits).toNat = w.val.val / 2 ^ bits
    rw [ulit_toNat' bits hb]
  · change ¬ (UInt256.ofNat bits).toNat ≥ 256
    rw [ulit_toNat' bits (lt_trans hbits (by decide +kernel))]
    omega

def vyperStringWords (length : UInt256) : UInt256 :=
  UInt256.shiftRight (UInt256.ofNat 31 + (length + UInt256.ofNat 32)) (UInt256.ofNat 5)

theorem vyperStringWords_toNat (length : UInt256) :
    (vyperStringWords length).toNat = ((length.toNat + 63) % UInt256.size) / 32 := by
  rw [vyperStringWords, u256_shiftRight_toNat_of_lt _ 5 (by omega), uadd_toNat, uadd_toNat]
  change ((31 + ((length.toNat + 32) % UInt256.size)) % UInt256.size) / 32 = _
  rw [Nat.add_mod_mod]
  congr 2
  omega

theorem vyperStringWords_normal (length : UInt256) (hlen : length.toNat ≤ 64) :
    (vyperStringWords length).toNat = (length.toNat + 63) / 32 := by
  rw [vyperStringWords_toNat, Nat.mod_eq_of_lt (by change length.toNat + 63 < 2 ^ 256; omega)]

theorem vyperStringWords_zero (length : UInt256)
    (hlo : UInt256.size - 63 ≤ length.toNat) (hhi : length.toNat ≤ UInt256.size - 32) :
    vyperStringWords length = ⟨0⟩ := by
  apply u256_inj
  rw [vyperStringWords_toNat]
  change ((length.toNat + 63) % UInt256.size) / 32 = 0
  have hlen : length.toNat < UInt256.size := length.val.isLt
  have hsize : 128 < UInt256.size := by decide +kernel
  rw [Nat.mod_eq_sub_mod (by omega : UInt256.size ≤ length.toNat + 63), Nat.mod_eq_of_lt (by omega)]
  omega

theorem vyperStringWords_top (length : UInt256) (hlen : UInt256.size - 31 ≤ length.toNat) :
    vyperStringWords length = ⟨1⟩ := by
  apply u256_inj
  rw [vyperStringWords_toNat]
  change ((length.toNat + 63) % UInt256.size) / 32 = 1
  have hlt : length.toNat < UInt256.size := length.val.isLt
  have hsize : 128 < UInt256.size := by decide +kernel
  rw [Nat.mod_eq_sub_mod (by omega : UInt256.size ≤ length.toNat + 63), Nat.mod_eq_of_lt (by omega)]
  omega

theorem vyperStringWords_oversize (length : UInt256)
    (hlo : 64 < length.toNat) (hhi : length.toNat < UInt256.size - 63) :
    3 < (vyperStringWords length).toNat := by
  rw [vyperStringWords_toNat, Nat.mod_eq_of_lt (by omega)]
  omega

theorem vyperStringPadding_toNat (length : UInt256) (hlen : length.toNat ≤ 64) :
    (UInt256.land (UInt256.sub ⟨0⟩ length) ⟨31⟩).toNat = ABI.paddedSize length.toNat - length.toNat := by
  by_cases hz : length.toNat = 0
  · have hzero : length = ⟨0⟩ := by apply u256_inj; exact hz
    rw [hzero]
    rfl
  · rw [u256_land_31_toNat, usub_toNat_underflow (by change 0 < length.toNat; omega)]
    change (2 ^ 256 + 0 - length.toNat) % 32 = 32 * ((length.toNat + 31) / 32) - length.toNat
    omega

theorem vyperStringOutputSize (length : UInt256) (hlen : length.toNat ≤ 64) :
    ((⟨32⟩ : UInt256) + UInt256.land (⟨32⟩ + length + ⟨31⟩) (UInt256.lnot ⟨31⟩)).toNat =
      64 + ABI.paddedSize length.toNat := by
  have hsum : ((⟨32⟩ : UInt256) + length + ⟨31⟩).toNat = length.toNat + 63 := by
    rw [uadd_toNat, uadd_toNat]
    change (((32 + length.toNat) % UInt256.size + 31) % UInt256.size) = _
    have hi : 32 + length.toNat < UInt256.size := by change 32 + length.toNat < 2 ^ 256; omega
    rw [Nat.mod_eq_of_lt hi]
    rw [Nat.mod_eq_of_lt (by change 32 + length.toNat + 31 < 2 ^ 256; omega)]
    omega
  rw [uadd_toNat, longDataCutoff_toNat, hsum]
  change (32 + ((length.toNat + 63) / 32) * 32) % UInt256.size = _
  rw [Nat.mod_eq_of_lt (by change 32 + ((length.toNat + 63) / 32) * 32 < 2 ^ 256; omega)]
  change 32 + ((length.toNat + 63) / 32) * 32 = 64 + 32 * ((length.toNat + 31) / 32)
  omega

end Benchmarks.CurveVault
