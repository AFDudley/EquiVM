import Benchmarks.EAS.EAS.WordArrayStore
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: a word write outside an initialized word array preserves its contents.
theorem memoryWords_write_disjoint (mem : ByteArray) (off len dst : Nat) (word : UInt256)
    (hb : off+32*len < UInt256.size) (hin : off+32*len ≤ mem.size)
    (hd : off+32*len ≤ dst ∨ dst+32 ≤ off) :
    memoryWords (Reasoning.Theory.writeWord mem dst word) off len = memoryWords mem off len := by
  apply List.ext_getElem (by simp only [memoryWords_length])
  intro i hi hi'
  have hi : i < len := by simpa only [memoryWords_length] using hi
  rw [memoryWords_get _ off len i hi,memoryWords_get _ off len i hi]
  have hn : (UInt256.ofNat (off+32*i)).toNat = off+32*i := ulit_toNat' _ (by omega)
  rcases hd with hd | hd
  · exact memLoad_write_below _ _ _ _ (by rw [hn]; omega) (by rw [hn]; omega)
  · exact memLoad_write_above _ _ _ _ (by rw [hn]; omega) (by rw [hn]; omega)

theorem WordArrayMemoryView.write_disjoint {mem : ByteArray} {ptr : UInt256}
    {words : List UInt256} {limit : Nat} (h : WordArrayMemoryView mem ptr words limit)
    (dst : Nat) (word : UInt256) (hb : limit < UInt256.size)
    (hd : ptr.toNat+32+32*words.length ≤ dst ∨ dst+32 ≤ ptr.toNat) :
    WordArrayMemoryView (Reasoning.Theory.writeWord mem dst word) ptr words limit := by
  refine ⟨h.low,h.span,?_,?_,?_⟩
  · rw [writeWord_sparse_size]
    exact le_trans h.covered (Nat.le_max_left _ _)
  · have hc := h.covered
    rcases hd with hd | hd
    · exact (memLoad_write_below _ _ _ _ (by omega) (by omega)).trans h.length
    · exact (memLoad_write_above _ _ _ _ hd (by omega)).trans h.length
  · rw [memoryWords_write_disjoint _ _ _ _ _ (by have := h.span; omega) h.covered
      (hd.elim Or.inl (fun hd => Or.inr (by omega)))]
    exact h.words

end Benchmarks.EAS.EAS
