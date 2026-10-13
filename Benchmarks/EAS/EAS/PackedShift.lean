import Benchmarks.EAS.EAS.PackedWord
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: a word shift retains the low source bits and appends zero bits.
theorem shiftLeft_toNat_mod (w : UInt256) (k : Nat) (hk : k < 256) :
    (UInt256.shiftLeft w (UInt256.ofNat k)).toNat = w.toNat % 2^(256-k) * 2^k := by
  have hkw : (UInt256.ofNat k).toNat = k := ulit_toNat' _ (by change k < 2^256; omega)
  have hm : UInt256.size = 2^(256-k)*2^k := by
    rw [← Nat.pow_add]
    change 2^256 = 2^(256-k+k)
    congr 1
    omega
  unfold UInt256.shiftLeft
  rw [if_neg (by change ¬ (UInt256.ofNat k).toNat ≥ 256; rw [hkw]; omega)]
  change (w.toNat <<< (UInt256.ofNat k).toNat) % UInt256.size = _
  rw [hkw,Nat.shiftLeft_eq,hm,Nat.mul_mod_mul_right]

-- GENERALIZES Reasoning.Theory.ctorAddressHighShift to any shifted word and width.
theorem shiftLeft_highMask (w : UInt256) (k : Nat) (hk : k < 256) :
    UInt256.land (UInt256.ofNat (2^256-2^k)) (UInt256.shiftLeft w (UInt256.ofNat k)) =
      UInt256.shiftLeft w (UInt256.ofNat k) := by
  rw [u256_land_comm]
  apply u256_land_high_mask_eq_self (hk := by omega)
  rw [shiftLeft_toNat_mod w k hk]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left _ _)

-- LIBRARY CANDIDATE: truncating source bits discarded by SHL leaves its result unchanged.
theorem shiftLeft_lowMask (w : UInt256) (k : Nat) (hk : k < 256) :
    UInt256.shiftLeft (UInt256.land w (UInt256.ofNat (2^(256-k)-1))) (UInt256.ofNat k) =
      UInt256.shiftLeft w (UInt256.ofNat k) := by
  apply u256_inj
  rw [shiftLeft_toNat_mod _ k hk,shiftLeft_toNat_mod _ k hk,uland_toNat]
  have hm : 2^(256-k)-1 < UInt256.size := by
    have hp : (2 : Nat)^(256-k) ≤ 2^256 := Nat.pow_le_pow_right (by decide) (by omega)
    have hz : 0 < (2 : Nat)^(256-k) := by positivity
    change 2^(256-k)-1 < 2^256
    omega
  rw [ulit_toNat' _ hm]
  change (Nat.land w.toNat (2^(256-k)-1)) % 2^(256-k) * 2^k = _
  rw [nat_land_mask_eq_mod,Nat.mod_mod]

end Benchmarks.EAS.EAS
