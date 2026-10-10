import Benchmarks.EAS.EAS.RevocationRequest
import Benchmarks.EAS.EAS.WordArrayMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

structure RevocationRequestMemoryView (mem : ByteArray) (ptr : UInt256) (r : RevocationRequestRecord) : Prop where
  low : 96 ≤ ptr.toNat
  covered : ptr.toNat+64 ≤ mem.size
  uid : memLoad ptr mem = r.uid
  value : memLoad (ptr+UInt256.ofNat 32) mem = r.value

theorem RevocationRequestMemoryView.preserve {before after : ByteArray} {ptr : UInt256}
    {r : RevocationRequestRecord} {limit : Nat} (h : RevocationRequestMemoryView before ptr r)
    (hp : MemoryPrefix before after limit) (he : ptr.toNat+64 ≤ limit) (hb : limit < UInt256.size) :
    RevocationRequestMemoryView after ptr r := by
  have ho : (ptr+UInt256.ofNat 32).toNat = ptr.toNat+32 := uadd_word_ofNat_toNat _ _ (by omega)
  have hc := h.covered
  have hl := h.low
  exact ⟨h.low,le_trans h.covered hp.size,
    (memLoad_of_prefix hp _ h.low (by omega) (by omega)).trans h.uid,
    (memLoad_of_prefix hp _ (by rw [ho]; omega) (by rw [ho]; omega) (by rw [ho]; omega)).trans h.value⟩

structure RevocationRequestArrayMemoryView (mem : ByteArray) (array : UInt256)
    (rs : List RevocationRequestRecord) (limit : Nat) : Prop where
  low : 96 ≤ array.toNat
  span : array.toNat+32+32*rs.length ≤ limit
  covered : array.toNat+32+32*rs.length ≤ mem.size
  length : memLoad array mem = UInt256.ofNat rs.length
  requests : ∀ i (hi : i < rs.length), ∃ ptr,
    memLoad (UInt256.ofNat (array.toNat+32+32*i)) mem = ptr ∧
    RevocationRequestMemoryView mem ptr rs[i] ∧ ptr.toNat+64 ≤ limit

theorem RevocationRequestArrayMemoryView.preserve {before after : ByteArray} {array : UInt256}
    {rs : List RevocationRequestRecord} {limit : Nat}
    (h : RevocationRequestArrayMemoryView before array rs limit) (hp : MemoryPrefix before after limit)
    (hb : limit < UInt256.size) : RevocationRequestArrayMemoryView after array rs limit := by
  have hs := h.span
  have hc := h.covered
  refine ⟨h.low,h.span,le_trans h.covered hp.size,?_,?_⟩
  · exact (memLoad_of_prefix hp _ h.low (by omega) (by omega)).trans h.length
  · intro i hi
    obtain ⟨ptr,hr,hv,he⟩ := h.requests i hi
    refine ⟨ptr,?_,hv.preserve hp he hb,he⟩
    have hn : (UInt256.ofNat (array.toNat+32+32*i)).toNat = array.toNat+32+32*i := ulit_toNat' _ (by omega)
    exact (memLoad_of_prefix hp _ (by rw [hn]; have := h.low; omega) (by rw [hn]; omega) (by rw [hn]; omega)).trans hr


theorem RevocationRequestArrayMemoryView.mono {mem : ByteArray} {array : UInt256}
    {rs : List RevocationRequestRecord} {limit next : Nat}
    (h : RevocationRequestArrayMemoryView mem array rs limit) (hh : limit ≤ next) :
    RevocationRequestArrayMemoryView mem array rs next := by
  refine ⟨h.low,le_trans h.span hh,h.covered,h.length,?_⟩
  intro i hi
  obtain ⟨ptr,hr,hv,he⟩ := h.requests i hi
  exact ⟨ptr,hr,hv,le_trans he hh⟩

end Benchmarks.EAS.EAS

