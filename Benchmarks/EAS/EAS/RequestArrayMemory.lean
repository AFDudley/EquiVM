import Benchmarks.EAS.EAS.RequestMemory
import Benchmarks.EAS.EAS.MemoryArrayIndex
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

structure AttestationRequestArrayMemoryView (mem : ByteArray) (array : UInt256) (rs : List AttestationRequestRecord) (limit : Nat) : Prop where
  low : 96 ≤ array.toNat
  span : array.toNat+32+32*rs.length ≤ limit
  covered : array.toNat+32+32*rs.length ≤ mem.size
  length : memLoad array mem = UInt256.ofNat rs.length
  requests : ∀ i (hi : i < rs.length), ∃ ptr dataPtr,
    memLoad (UInt256.ofNat (array.toNat+32+32*i)) mem = ptr ∧
    AttestationRequestMemoryView mem ptr dataPtr rs[i] ∧
    ptr.toNat+192 ≤ limit ∧ dataPtr.toNat+32+32*((rs[i].data.size+31)/32) ≤ limit

theorem AttestationRequestArrayMemoryView.preserve {before after : ByteArray} {array : UInt256}
    {rs : List AttestationRequestRecord} {limit : Nat}
    (h : AttestationRequestArrayMemoryView before array rs limit) (hp : MemoryPrefix before after limit)
    (hb : limit < UInt256.size) : AttestationRequestArrayMemoryView after array rs limit := by
  have hs := h.span
  have hc := h.covered
  refine ⟨h.low,h.span,le_trans h.covered hp.size,?_,?_⟩
  · exact (memLoad_of_prefix hp _ h.low (by omega) (by omega)).trans h.length
  · intro i hi
    obtain ⟨ptr,dp,hp0,hv,he,hd⟩ := h.requests i hi
    refine ⟨ptr,dp,?_,hv.preserve hp he hd hb,he,hd⟩
    have hn : (UInt256.ofNat (array.toNat+32+32*i)).toNat = array.toNat+32+32*i := ulit_toNat' _ (by omega)
    exact (memLoad_of_prefix hp _ (by rw [hn]; have := h.low; omega) (by rw [hn]; omega) (by rw [hn]; omega)).trans hp0

theorem AttestationRequestArrayMemoryView.mono {mem : ByteArray} {array : UInt256}
    {rs : List AttestationRequestRecord} {limit limit' : Nat}
    (h : AttestationRequestArrayMemoryView mem array rs limit) (hh : limit ≤ limit') :
    AttestationRequestArrayMemoryView mem array rs limit' := by
  refine ⟨h.low,le_trans h.span hh,h.covered,h.length,?_⟩
  intro i hi
  obtain ⟨ptr,dp,hp,hv,he,hd⟩ := h.requests i hi
  exact ⟨ptr,dp,hp,hv,le_trans he hh,le_trans hd hh⟩

end Benchmarks.EAS.EAS
