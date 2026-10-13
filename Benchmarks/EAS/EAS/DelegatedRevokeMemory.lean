import Benchmarks.EAS.EAS.VerifyRevokeSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

structure DelegatedRevokeMemoryView (mem : ByteArray) (ptr dataPtr sigPtr : UInt256)
    (r : DelegatedRevocationRecord) (limit : Nat) : Prop where
  low : 96 ≤ ptr.toNat
  covered : ptr.toNat+128 ≤ mem.size
  span : ptr.toNat+128 ≤ limit
  schema : memLoad ptr mem = r.schema
  dataPointer : memLoad (ptr+UInt256.ofNat 32) mem = dataPtr
  sigPointer : memLoad (ptr+UInt256.ofNat 64) mem = sigPtr
  revoker : UInt256.land (memLoad (ptr+UInt256.ofNat 96) mem) solcAddrMask = UInt256.ofNat r.revoker.val
  data : RevocationRequestMemoryView mem dataPtr r.data
  dataEnd : dataPtr.toNat+64 ≤ limit
  signature : SignatureMemoryView mem sigPtr r.signature
  sigEnd : sigPtr.toNat+96 ≤ limit

theorem DelegatedRevokeMemoryView.preserve {before after : ByteArray} {ptr dataPtr sigPtr : UInt256}
    {r : DelegatedRevocationRecord} {limit : Nat}
    (h : DelegatedRevokeMemoryView before ptr dataPtr sigPtr r limit) (hp : MemoryPrefix before after limit)
    (hb : limit < UInt256.size) : DelegatedRevokeMemoryView after ptr dataPtr sigPtr r limit := by
  have hc := h.covered
  have he := h.span
  have hl := h.low
  have hr (n : Nat) (hn : n ≤ 96) : memLoad (ptr+UInt256.ofNat n) after = memLoad (ptr+UInt256.ofNat n) before := by
    have ho : (ptr+UInt256.ofNat n).toNat = ptr.toNat+n := uadd_word_ofNat_toNat _ _ (by omega)
    exact memLoad_of_prefix hp _ (by rw [ho]; omega) (by rw [ho]; omega) (by rw [ho]; omega)
  refine ⟨hl,le_trans hc hp.size,he,?_,?_,?_,?_,h.data.preserve hp h.dataEnd hb,h.dataEnd,
    h.signature.preserve hp h.sigEnd hb,h.sigEnd⟩
  · exact (memLoad_of_prefix hp _ hl (by omega) (by omega)).trans h.schema
  · exact (hr 32 (by decide)).trans h.dataPointer
  · exact (hr 64 (by decide)).trans h.sigPointer
  · rw [hr 96 (by decide)]; exact h.revoker

theorem DelegatedRevokeMemoryView.mono {mem : ByteArray} {ptr dataPtr sigPtr : UInt256}
    {r : DelegatedRevocationRecord} {limit next : Nat}
    (h : DelegatedRevokeMemoryView mem ptr dataPtr sigPtr r limit) (hle : limit ≤ next) :
    DelegatedRevokeMemoryView mem ptr dataPtr sigPtr r next :=
  ⟨h.low,h.covered,le_trans h.span hle,h.schema,h.dataPointer,h.sigPointer,h.revoker,h.data,le_trans h.dataEnd hle,
    h.signature,le_trans h.sigEnd hle⟩

end Benchmarks.EAS.EAS
