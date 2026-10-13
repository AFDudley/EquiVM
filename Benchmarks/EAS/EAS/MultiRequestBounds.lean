import Benchmarks.EAS.EAS.MultiRequestControl
import Benchmarks.EAS.EAS.CalldataSignedStride
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- GENERALIZES nestedPayload_of_bound to an arbitrary, possibly wrapping header address.
theorem calldataArrayExtent_signed {cd : ByteArray} {header : UInt256}
    (hsize : cd.size < 2^255) (hlen : (calldataWord cd header.toNat).toNat ≤ 2^64-1)
    (hend : UInt256.gt ((header+UInt256.ofNat 32)+UInt256.shiftLeft (calldataWord cd header.toNat) (UInt256.ofNat 5))
      (UInt256.ofNat cd.size) = ⟨0⟩) :
    UInt256.sgt ((UInt256.ofNat 32)+header)
      (UInt256.sub (UInt256.ofNat cd.size) (UInt256.shiftLeft (calldataWord cd header.toNat) (UInt256.ofNat 5))) = ⟨0⟩ := by
  have hshift := wordShiftLeft_nat (calldataWord cd header.toNat) 5 (by decide)
  rw [hshift] at hend ⊢
  exact calldataArrayExtent_signed_stride hsize (by omega) hend

theorem requestArrayAccessValid_of_decode {cd : ByteArray} {root : UInt256} {rs : List AttestationRequestRecord}
    (hsize : cd.size < 2^255) (hd : decodeMultiRequestAt cd root = some rs) : requestArrayAccessValid cd root := by
  unfold decodeMultiRequestAt at hd
  by_cases hr : requestArrayReferenceValid cd root
  · rw [if_pos hr] at hd
    have hh := (decodeRequestArray_facts (by omega) hd).1
    exact ⟨hr,hh.1,calldataArrayExtent_signed hsize hh.1 hh.2⟩
  · rw [if_neg hr] at hd
    contradiction

end Benchmarks.EAS.EAS
