import Benchmarks.EAS.EAS.BytesLongTail
import Benchmarks.EAS.EAS.BytesShortWord
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: the shifted low-byte length mask retains the final bytes prefix.
theorem bytesLongTailMask (len : UInt256) :
    UInt256.lnot (UInt256.shiftRight (UInt256.ofNat (2^256-1))
      (UInt256.land (UInt256.shiftLeft len (UInt256.ofNat 3)) (UInt256.ofNat 248))) =
      UInt256.ofNat (2^256-2^(8*(32-len.toNat%32))) := by
  have hrem : (UInt256.land len ⟨31⟩).toNat < 32 := by
    rw [u256_land_31_toNat]
    exact Nat.mod_lt _ (by decide)
  have hs : UInt256.land (UInt256.shiftLeft len (UInt256.ofNat 3)) (UInt256.ofNat 248) =
      UInt256.mul ⟨8⟩ (UInt256.land len ⟨31⟩) := by
    apply u256_inj
    have h := shiftLeft_maskSlice_toNat len 3 5 (by decide) (by decide)
    change (UInt256.land (UInt256.shiftLeft len (UInt256.ofNat 3)) (UInt256.ofNat 248)).toNat = len.toNat%32*8 at h
    rw [h,u256_mul_toNat,u256_land_31_toNat]
    change len.toNat%32*8 = (8*(len.toNat%32))%UInt256.size
    have hm : 8*(len.toNat%32) < UInt256.size := by
      have := Nat.mod_lt len.toNat (by decide : 0<32)
      change 8*(len.toNat%32)<2^256
      omega
    rw [Nat.mod_eq_of_lt hm]
    omega
  rw [hs]
  change UInt256.lnot (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.mul ⟨8⟩ (UInt256.land len ⟨31⟩))) = _
  rw [shortPackedHeader_mask_of_short hrem,u256_land_31_toNat]
  rw [show 256-8*(len.toNat%32) = 8*(32-len.toNat%32) from by have := Nat.mod_lt len.toNat (by decide : 0<32); omega]

-- LIBRARY CANDIDATE: the shift-based long-bytes header equals the source encoding.
theorem bytesLongHeader_eq (len : UInt256) (hlong : ¬len.toNat<32) (hb : len.toNat ≤ solcMaxU64) :
    UInt256.shiftLeft len (UInt256.ofNat 1)+⟨1⟩ = solidityBytesHeaderWord len.toNat := by
  rw [wordShiftLeft_mul len 1 (by decide),solidityBytesHeaderWord_eq_len_mul_two_add_one rfl hlong hb]
  rfl

end Benchmarks.EAS.EAS
