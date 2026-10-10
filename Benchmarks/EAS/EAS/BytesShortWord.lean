import Benchmarks.EAS.EAS.BytesWordMask
import Benchmarks.EAS.EAS.WordShiftMul
import Benchmarks.EAS.EAS.BytesShortEVM
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem bytesShortEVMWord_eq (payload len : UInt256) (hl : len.toNat < 32) :
    bytesShortEVMWord payload len = UInt256.lor
      (uInt256OfByteArray ((payload.toByteArray.extract 0 len.toNat).readWithPadding 0 32))
      (UInt256.ofNat (len.toNat*2)) := by
  have hm : UInt256.lnot (UInt256.shiftRight (UInt256.ofNat (2^256-1)) (UInt256.shiftLeft len (UInt256.ofNat 3))) =
      UInt256.ofNat (2^256-2^(8*(32-len.toNat))) := by
    rw [wordShiftLeft_mul len 3 (by decide),u256_mul_comm len]
    change UInt256.lnot (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.mul ⟨8⟩ len)) = _
    rw [shortPackedHeader_mask_of_short hl]
    rw [show 256-8*len.toNat = 8*(32-len.toNat) from by omega]
  have hh : UInt256.shiftLeft len (UInt256.ofNat 1) = UInt256.ofNat (len.toNat*2) := by
    calc
      UInt256.shiftLeft len (UInt256.ofNat 1) = UInt256.shiftLeft (UInt256.ofNat len.toNat) (UInt256.ofNat 1) := by rw [u256_ofNat_toNat]
      _ = UInt256.ofNat (len.toNat*2) := by
        simpa only [Nat.mul_comm] using shiftLeft1_ofNat_eq (n := len.toNat) (by change 2*len.toNat < 2^256; omega)
  rw [bytesShortEVMWord,hm,hh,wordPrefixMask payload len.toNat hl]

end Benchmarks.EAS.EAS
