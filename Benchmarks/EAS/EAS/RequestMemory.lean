import Benchmarks.EAS.EAS.AttestationRequest
import Benchmarks.EAS.EAS.RecordMemory
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

structure AttestationRequestMemoryView (mem : ByteArray) (ptr dataPtr : UInt256) (r : AttestationRequestRecord) : Prop where
  low : 96 ≤ ptr.toNat
  dataLow : 96 ≤ dataPtr.toNat
  covered : ptr.toNat+192 ≤ mem.size
  dataCovered : dataPtr.toNat+32+32*((r.data.size+31)/32) ≤ mem.size
  recipient : UInt256.land solcAddrMask (memLoad ptr mem) = UInt256.ofNat r.recipient.val
  expiration : UInt256.land easUint64Mask (memLoad (ptr+UInt256.ofNat 32) mem) = r.expirationTime
  revocable : UInt256.isZero (UInt256.isZero (memLoad (ptr+UInt256.ofNat 64) mem)) = r.revocable.toUInt256
  refUID : memLoad (ptr+UInt256.ofNat 96) mem = r.refUID
  pointer : memLoad (ptr+UInt256.ofNat 128) mem = dataPtr
  value : memLoad (ptr+UInt256.ofNat 160) mem = r.value
  length : memLoad dataPtr mem = UInt256.ofNat r.data.size
  payload : mem.readWithPadding (dataPtr.toNat+32) r.data.size = r.data

theorem AttestationRequestMemoryView.preserve {before after : ByteArray} {ptr dataPtr : UInt256}
    {r : AttestationRequestRecord} {limit : Nat} (h : AttestationRequestMemoryView before ptr dataPtr r)
    (hp : MemoryPrefix before after limit) (hsource : ptr.toNat+192 ≤ limit)
    (hdata : dataPtr.toNat+32+32*((r.data.size+31)/32) ≤ limit) (hb : limit < UInt256.size) :
    AttestationRequestMemoryView after ptr dataPtr r := by
  have hr (n : Nat) (hn : n ≤ 160) : memLoad (ptr+UInt256.ofNat n) after = memLoad (ptr+UInt256.ofNat n) before := by
    have he := uadd_word_ofNat_toNat ptr n (by omega : ptr.toNat+n < UInt256.size)
    exact memLoad_of_prefix hp _ (by rw [he]; have := h.low; omega)
      (by rw [he]; omega) (by rw [he]; have := h.covered; omega)
  have hr0 := memLoad_of_prefix hp ptr h.low (by omega) (by have := h.covered; omega)
  refine ⟨h.low,h.dataLow,le_trans h.covered hp.size,le_trans h.dataCovered hp.size,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hr0]; exact h.recipient
  · rw [hr 32 (by decide)]; exact h.expiration
  · rw [hr 64 (by decide)]; exact h.revocable
  · exact (hr 96 (by decide)).trans h.refUID
  · exact (hr 128 (by decide)).trans h.pointer
  · exact (hr 160 (by decide)).trans h.value
  · exact (memLoad_of_prefix hp dataPtr h.dataLow (by omega) (by have := h.dataCovered; omega)).trans h.length
  · exact (memoryPrefix_read_prefix hp (dataPtr.toNat+32) ((r.data.size+31)/32) r.data.size
      (by have := h.dataLow; omega) hdata h.dataCovered (by omega) (by omega)).trans h.payload

end Benchmarks.EAS.EAS
