import Benchmarks.EAS.EAS.WordArrayEVM
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: a bounded offset's complete-word guard, including the signed size check.
theorem arrayHeaderGuard {cd : ByteArray} {off : UInt256}
    (ho : off.toNat ≤ solcMaxU64) (hsize : cd.size < UInt256.size) :
    UInt256.isZero (UInt256.slt ((UInt256.ofNat 4 + off) + UInt256.ofNat 31) (UInt256.ofNat cd.size)) =
      UInt256.fromBool (!decide (off.toNat + 36 ≤ cd.size ∧ cd.size < 2^255)) := by
  have hsmall : off.toNat + 36 < 2^255 := by change off.toNat ≤ 18446744073709551615 at ho; omega
  have hleft : ((UInt256.ofNat 4 + off) + UInt256.ofNat 31).toNat = off.toNat + 35 := by
    change (((⟨4⟩ : UInt256) + off) + ⟨31⟩).toNat = _
    rw [uadd_toNat, add4_word_toNat off ho]
    change (4 + off.toNat + 31) % UInt256.size = off.toNat + 35
    rw [Nat.mod_eq_of_lt (by change 4 + off.toNat + 31 < 2^256; omega)]
    omega
  have hright : (UInt256.ofNat cd.size).toNat = cd.size := ofNat_toNat_lt _ hsize
  have hc : UInt256.sltBool ((UInt256.ofNat 4 + off) + UInt256.ofNat 31) (UInt256.ofNat cd.size) =
      decide (off.toNat + 36 ≤ cd.size ∧ cd.size < 2^255) := by
    have hbridge : UInt256.sltBool ((UInt256.ofNat 4 + off) + UInt256.ofNat 31) (UInt256.ofNat cd.size) =
        ABI.Solc08Calldata.solcSLT (((UInt256.ofNat 4 + off) + UInt256.ofNat 31).toNat) (UInt256.ofNat cd.size).toNat := by
      unfold ABI.Solc08Calldata.solcSLT
      change _ = decide (EVM.signed (UInt256.ofNat (((UInt256.ofNat 4 + off) + UInt256.ofNat 31).toNat)) <
        EVM.signed (UInt256.ofNat (UInt256.ofNat cd.size).toNat))
      rw [u256_ofNat_toNat, u256_ofNat_toNat, sltBool_signed]
    rw [hbridge, hleft, hright, solcSLT_smallLeft (by omega) hsize]
    congr 1
  change UInt256.isZero (UInt256.fromBool _) = _
  rw [hc]
  cases decide (off.toNat + 36 ≤ cd.size ∧ cd.size < 2^255) <;> rfl

-- LIBRARY CANDIDATE: the bounded array extent has no word wraparound.
theorem arrayExtent_toNat {off length : UInt256}
    (ho : off.toNat ≤ solcMaxU64) (hn : length.toNat ≤ solcMaxU64) :
    (((UInt256.shiftLeft length (UInt256.ofNat 5)) + (UInt256.ofNat 4 + off)) + UInt256.ofNat 32).toNat =
      off.toNat + 36 + 32 * length.toNat := by
  have hsmall : off.toNat + 68 + 32 * length.toNat < UInt256.size := by
    change off.toNat ≤ 18446744073709551615 at ho
    change length.toNat ≤ 18446744073709551615 at hn
    change off.toNat + 68 + 32 * length.toNat < 2^256
    omega
  have hshift : (UInt256.shiftLeft length (UInt256.ofNat 5)).toNat = 32 * length.toNat := by
    conv_lhs => rw [← u256_ofNat_toNat length]
    change ((UInt256.ofNat length.toNat).shiftLeft ⟨5⟩).toNat = _
    rw [shiftLeft5_ofNat_eq (by omega), ofNat_toNat_lt _ (by omega)]
  rw [uadd_toNat, uadd_toNat, hshift]
  change ((32 * length.toNat + ((⟨4⟩ : UInt256) + off).toNat) % UInt256.size + 32) % UInt256.size = _
  rw [add4_word_toNat off ho]
  change ((32 * length.toNat + (4 + off.toNat)) % UInt256.size + 32) % UInt256.size = _
  rw [Nat.mod_eq_of_lt (show 32 * length.toNat + (4 + off.toNat) < UInt256.size by omega),
    Nat.mod_eq_of_lt (by omega)]
  omega

end Benchmarks.EAS.EAS
