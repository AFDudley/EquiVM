import Benchmarks.EAS.EAS.RecordEncoding
import Benchmarks.EAS.EAS.CallMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

structure AttestationMemoryView (mem : ByteArray) (src dataPtr : UInt256) (a : AttestationRecord) : Prop where
  sourceLow : 96 ≤ src.toNat
  dataLow : 96 ≤ dataPtr.toNat
  sourceCovered : src.toNat+320 ≤ mem.size
  dataCovered : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ mem.size
  pointer : memLoad (src+UInt256.ofNat 288) mem = dataPtr
  length : memLoad dataPtr mem = UInt256.ofNat a.data.size
  fields : attestationEncodeHeadWords mem src = a.words ++ [UInt256.ofNat 320]
  payload : mem.readWithPadding (dataPtr.toNat+32) a.data.size = a.data

theorem AttestationMemoryView.preserve {before after : ByteArray} {src dataPtr : UInt256}
    {a : AttestationRecord} {limit : Nat} (h : AttestationMemoryView before src dataPtr a)
    (hp : MemoryPrefix before after limit) (hsource : src.toNat+320 ≤ limit)
    (hdata : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ limit) (hb : limit < UInt256.size) :
    AttestationMemoryView after src dataPtr a := by
  have hs : (src+UInt256.ofNat 288).toNat = src.toNat+288 := uadd_word_ofNat_toNat src 288 (by omega)
  refine ⟨h.sourceLow, h.dataLow, le_trans h.sourceCovered hp.size, le_trans h.dataCovered hp.size, ?_, ?_, ?_, ?_⟩
  · exact (memLoad_of_prefix hp _ (by rw [hs]; have h := h.sourceLow; omega)
      (by rw [hs]; omega) (by rw [hs]; have h := h.sourceCovered; omega)).trans h.pointer
  · exact (memLoad_of_prefix hp dataPtr h.dataLow (by omega) (by have h := h.dataCovered; omega)).trans h.length
  · exact (attestationHeadWords_of_prefix hp src h.sourceLow hsource h.sourceCovered (by omega)).trans h.fields
  · exact (memoryPrefix_read_prefix hp (dataPtr.toNat+32) ((a.data.size+31)/32) a.data.size
      (by have h := h.dataLow; omega) hdata h.dataCovered (by omega) (by omega)).trans h.payload

end Benchmarks.EAS.EAS
