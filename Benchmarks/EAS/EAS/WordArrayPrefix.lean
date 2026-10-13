import Benchmarks.EAS.EAS.WordArrayStore
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: a word array whose initialized prefix grows with the copy cursor.
structure WordArrayPrefixView (mem : ByteArray) (ptr : UInt256) (words : List UInt256) (filled limit : Nat) : Prop where
  low : 96 ≤ ptr.toNat
  progress : filled ≤ words.length
  span : ptr.toNat+32+32*words.length ≤ limit
  covered : ptr.toNat+32+32*filled ≤ mem.size
  length : memLoad ptr mem = UInt256.ofNat words.length
  words : ∀ i (hi : i < filled), memLoad (UInt256.ofNat (ptr.toNat+32+32*i)) mem = words[i]

theorem WordArrayPrefixView.set {mem : ByteArray} {ptr : UInt256} {words : List UInt256} {filled limit : Nat}
    (h : WordArrayPrefixView mem ptr words filled limit) (hi : filled < words.length)
    (word : UInt256) (hb : limit < UInt256.size) :
    WordArrayPrefixView (Reasoning.Theory.writeWord mem (ptr.toNat+32+32*filled) word)
      ptr (words.set filled word) (filled+1) limit := by
  have hs := h.span
  have hc := h.covered
  refine ⟨h.low,by rw [List.length_set]; omega,by simpa only [List.length_set] using h.span,?_,?_,?_⟩
  · rw [writeWord_sparse_size]; omega
  · rw [List.length_set]
    exact (memLoad_write_below _ _ _ _ (by omega) (by omega)).trans h.length
  · intro j hj
    have hptr : (UInt256.ofNat (ptr.toNat+32+32*j)).toNat = ptr.toNat+32+32*j := ulit_toNat' _ (by omega)
    by_cases he : j = filled
    · subst j
      rw [List.getElem_set_self]
      apply mloadWordValue_of_readWithPadding
      · rw [hptr,writeWord_sparse_size]; omega
      · rw [hptr]; exact writeWord_sparse_read_back _ _ _
    · rw [List.getElem_set_ne (Ne.symm he)]
      exact (memLoad_write_below _ _ _ _ (by rw [hptr]; omega) (by rw [hptr]; omega)).trans (h.words j (by omega))

theorem WordArrayPrefixView.finish {mem : ByteArray} {ptr : UInt256} {words : List UInt256} {limit : Nat}
    (h : WordArrayPrefixView mem ptr words words.length limit) : WordArrayMemoryView mem ptr words limit := by
  refine ⟨h.low,h.span,h.covered,h.length,?_⟩
  apply List.ext_getElem (memoryWords_length ..)
  intro i hi hi'
  rw [memoryWords_get _ _ _ _ hi']
  exact h.words i hi'

-- LIBRARY CANDIDATE: a pointer table of initialized word arrays.
structure WordArrayArrayMemoryView (mem : ByteArray) (ptr : UInt256) (groups : List (List UInt256)) (limit : Nat) : Prop where
  low : 96 ≤ ptr.toNat
  span : ptr.toNat+32+32*groups.length ≤ limit
  covered : ptr.toNat+32+32*groups.length ≤ mem.size
  length : memLoad ptr mem = UInt256.ofNat groups.length
  arrays : ∀ i (hi : i < groups.length), ∃ p,
    memLoad (UInt256.ofNat (ptr.toNat+32+32*i)) mem = p ∧ WordArrayMemoryView mem p groups[i] limit

theorem WordArrayArrayMemoryView.preserve {mem after : ByteArray} {ptr : UInt256} {groups : List (List UInt256)} {limit : Nat}
    (h : WordArrayArrayMemoryView mem ptr groups limit) (hp : MemoryPrefix mem after limit)
    (hb : limit < UInt256.size) : WordArrayArrayMemoryView after ptr groups limit := by
  have hs := h.span
  have hc := h.covered
  refine ⟨h.low,h.span,le_trans h.covered hp.size,?_,?_⟩
  · exact (memLoad_of_prefix hp ptr h.low (by omega) (by omega)).trans h.length
  · intro i hi
    obtain ⟨p,hptr,hv⟩ := h.arrays i hi
    have hn : (UInt256.ofNat (ptr.toNat+32+32*i)).toNat = ptr.toNat+32+32*i := ulit_toNat' _ (by omega)
    exact ⟨p,(memLoad_of_prefix hp _ (by rw [hn]; have := h.low; omega) (by rw [hn]; omega)
      (by rw [hn]; omega)).trans hptr,hv.preserve hp hb⟩

end Benchmarks.EAS.EAS
