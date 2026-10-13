import Benchmarks.EAS.EAS.VerifyAttestSource
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

structure DelegatedAttestMemoryView (mem : ByteArray) (ptr dataPtr bytesPtr sigPtr : UInt256)
    (r : DelegatedAttestationRecord) (limit : Nat) : Prop where
  low : 96 ≤ ptr.toNat
  covered : ptr.toNat+128 ≤ mem.size
  span : ptr.toNat+128 ≤ limit
  schema : memLoad ptr mem = r.schema
  dataPointer : memLoad (ptr+UInt256.ofNat 32) mem = dataPtr
  sigPointer : memLoad (ptr+UInt256.ofNat 64) mem = sigPtr
  attester : UInt256.land (memLoad (ptr+UInt256.ofNat 96) mem) solcAddrMask = UInt256.ofNat r.attester.val
  data : AttestationRequestMemoryView mem dataPtr bytesPtr r.data
  dataEnd : dataPtr.toNat+192 ≤ limit
  bytesEnd : bytesPtr.toNat+32+32*((r.data.data.size+31)/32) ≤ limit
  signature : SignatureMemoryView mem sigPtr r.signature
  sigEnd : sigPtr.toNat+96 ≤ limit

theorem DelegatedAttestMemoryView.preserve {before after : ByteArray} {ptr dataPtr bytesPtr sigPtr : UInt256}
    {r : DelegatedAttestationRecord} {limit : Nat}
    (h : DelegatedAttestMemoryView before ptr dataPtr bytesPtr sigPtr r limit) (hp : MemoryPrefix before after limit)
    (hb : limit < UInt256.size) : DelegatedAttestMemoryView after ptr dataPtr bytesPtr sigPtr r limit := by
  have hc := h.covered
  have he := h.span
  have hl := h.low
  have hr (n : Nat) (hn : n ≤ 96) : memLoad (ptr+UInt256.ofNat n) after = memLoad (ptr+UInt256.ofNat n) before := by
    have ho : (ptr+UInt256.ofNat n).toNat = ptr.toNat+n := uadd_word_ofNat_toNat _ _ (by omega)
    exact memLoad_of_prefix hp _ (by rw [ho]; omega) (by rw [ho]; omega) (by rw [ho]; omega)
  refine ⟨hl,le_trans hc hp.size,he,?_,?_,?_,?_,h.data.preserve hp h.dataEnd h.bytesEnd hb,h.dataEnd,h.bytesEnd,
    h.signature.preserve hp h.sigEnd hb,h.sigEnd⟩
  · exact (memLoad_of_prefix hp _ hl (by omega) (by omega)).trans h.schema
  · exact (hr 32 (by decide)).trans h.dataPointer
  · exact (hr 64 (by decide)).trans h.sigPointer
  · rw [hr 96 (by decide)]; exact h.attester

theorem DelegatedAttestMemoryView.mono {mem : ByteArray} {ptr dataPtr bytesPtr sigPtr : UInt256}
    {r : DelegatedAttestationRecord} {limit next : Nat}
    (h : DelegatedAttestMemoryView mem ptr dataPtr bytesPtr sigPtr r limit) (hle : limit ≤ next) :
    DelegatedAttestMemoryView mem ptr dataPtr bytesPtr sigPtr r next :=
  ⟨h.low,h.covered,le_trans h.span hle,h.schema,h.dataPointer,h.sigPointer,h.attester,h.data,le_trans h.dataEnd hle,le_trans h.bytesEnd hle,
    h.signature,le_trans h.sigEnd hle⟩

end Benchmarks.EAS.EAS
