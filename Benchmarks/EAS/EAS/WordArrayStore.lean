import Benchmarks.EAS.EAS.MemoryArrayIndex
import Benchmarks.EAS.EAS.RecordUID
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: replacing one initialized memory word updates the corresponding list entry.
theorem memoryWords_set (mem : ByteArray) (off len i : Nat) (word : UInt256)
    (hi : i < len) (hb : off+32*len < UInt256.size) (hin : off+32*len ≤ mem.size) :
    memoryWords (Reasoning.Theory.writeWord mem (off+32*i) word) off len = (memoryWords mem off len).set i word := by
  apply List.ext_getElem (by simp only [memoryWords_length,List.length_set])
  intro j hj hj'
  have hjb : j < len := by simpa only [memoryWords_length] using hj
  rw [memoryWords_get _ off len j hjb]
  have hn : (UInt256.ofNat (off+32*j)).toNat = off+32*j := ulit_toNat' _ (by omega)
  by_cases he : i = j
  · subst i
    rw [List.getElem_set_self]
    exact mloadWordValue_of_readWithPadding (by rw [hn,writeWord_sparse_size]; omega)
      (by rw [hn]; exact writeWord_sparse_read_back _ _ _)
  · rw [List.getElem_set_ne he,memoryWords_get mem off len j hjb]
    rcases lt_or_gt_of_ne he with hij | hji
    · exact memLoad_write_above _ _ _ _ (by rw [hn]; omega) (by rw [hn]; omega)
    · exact memLoad_write_below _ _ _ _ (by rw [hn]; omega) (by rw [hn]; omega)

theorem WordArrayMemoryView.set {mem : ByteArray} {ptr : UInt256} {words : List UInt256} {limit : Nat}
    (h : WordArrayMemoryView mem ptr words limit) (i : Nat) (hi : i < words.length)
    (word : UInt256) (hb : limit < UInt256.size) :
    WordArrayMemoryView (Reasoning.Theory.writeWord mem (ptr.toNat+32+32*i) word) ptr (words.set i word) limit := by
  refine ⟨h.low,?_,?_,?_,?_⟩
  · simpa only [List.length_set] using h.span
  · rw [List.length_set,writeWord_sparse_size]
    exact le_trans h.covered (Nat.le_max_left _ _)
  · rw [List.length_set]
    exact (memLoad_write_below _ _ _ _ (by omega) (by have := h.covered; omega)).trans h.length
  · rw [List.length_set,memoryWords_set _ _ _ _ _ hi (by have := h.span; omega) h.covered,h.words]

end Benchmarks.EAS.EAS
