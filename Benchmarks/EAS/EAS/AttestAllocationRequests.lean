import Benchmarks.EAS.EAS.AttestAllocationMemory
import Benchmarks.EAS.EAS.RequestRegion
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem attestAllocationMemory_requests {mem : ByteArray} {heap data : UInt256}
    {rs : List AttestationRequestRecord} (kind : AttestCallKind) (attester : UInt256)
    (h : AttestationRequestArrayRegion mem data rs 224 heap.toNat)
    (hh : heap.toNat ≤ 2^64-1) (hn : allocateNext heap.toNat 128 ≤ 2^64-1) :
    AttestationRequestArrayRegion (attestAllocationMemory kind mem heap data attester) data rs 224 heap.toNat := by
  have hlo := h.arrayLow
  have hspan := h.view.span
  have he : AttestationRequestArrayRegion (attestEntryMemory kind mem data attester) data rs 224 heap.toNat := by
    cases kind with
    | single => exact h
    | many => exact (h.write_below 192 data (by decide) heap.val.isLt).write_below 160 attester (by decide) heap.val.isLt
  have hp := (attestResultsMemory_view (attestEntryMemory kind mem data attester) heap (by omega) hh hn).1
  have ha := he.preserve hp heap.val.isLt
  cases kind with
  | single => exact ha
  | many => exact ha.write_below 128 (UInt256.ofNat (allocateNext heap.toNat 64)) (by decide) heap.val.isLt

end Benchmarks.EAS.EAS
