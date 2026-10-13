import Benchmarks.EAS.EAS.CalldataPayload
import Benchmarks.EAS.EAS.WordShiftMul
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- GENERALIZES calldataArrayExtent_complete to any bounded element stride.
theorem calldataArrayExtent_stride {cd : ByteArray} {header : UInt256} {stride : Nat}
    (hsize : cd.size < 2^255+4)
    (hprod : stride*(calldataWord cd header.toNat).toNat < 2^128)
    (hend : UInt256.gt ((header+UInt256.ofNat 32)+UInt256.ofNat (stride*(calldataWord cd header.toNat).toNat))
      (UInt256.ofNat cd.size) = ⟨0⟩) :
    (header+UInt256.ofNat 32).toNat+stride*(calldataWord cd header.toNat).toNat ≤ cd.size := by
  let len := calldataWord cd header.toNat
  have hd := ugt_eq_zero_to_le hend
  rw [ulit_toNat' cd.size (by change cd.size < 2^256; omega)] at hd
  by_cases hz : len.toNat = 0
  · change (header+UInt256.ofNat 32+UInt256.ofNat (stride*len.toNat)).toNat ≤ cd.size at hd
    simp only [hz,Nat.mul_zero,show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,u256_add_zero] at hd
    change (header+UInt256.ofNat 32).toNat+stride*len.toNat ≤ cd.size
    simpa only [hz,Nat.mul_zero,Nat.add_zero] using hd
  · have hs : header.toNat < cd.size := by
      by_contra h
      have hzero := calldataWord_zero_of_ge cd header.toNat (by omega)
      exact hz (congrArg UInt256.toNat hzero)
    have hh : (header+UInt256.ofNat 32).toNat = header.toNat+32 :=
      uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
    rw [uadd_word_ofNat_toNat _ _ (by rw [hh]; change _ < 2^256; omega)] at hd
    exact hd

theorem calldataArrayExtent_complete {cd : ByteArray} {header : UInt256}
    (hsize : cd.size < 2^255+4)
    (hlen : (calldataWord cd header.toNat).toNat ≤ 2^64-1)
    (hend : UInt256.gt ((header+UInt256.ofNat 32)+UInt256.shiftLeft (calldataWord cd header.toNat) (UInt256.ofNat 5))
      (UInt256.ofNat cd.size) = ⟨0⟩) :
    (header+UInt256.ofNat 32).toNat+32*(calldataWord cd header.toNat).toNat ≤ cd.size := by
  apply calldataArrayExtent_stride hsize (by omega)
  simpa only [wordShiftLeft_nat _ 5 (by decide),show 2^5 = 32 from rfl] using hend

end Benchmarks.EAS.EAS
