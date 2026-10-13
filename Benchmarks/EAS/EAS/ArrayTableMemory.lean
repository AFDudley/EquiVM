import Benchmarks.EAS.EAS.ArrayTableAllocate
import Benchmarks.EAS.EAS.WordArrayPrefix
import Benchmarks.EAS.EAS.ArrayDisjoint
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: a pointer table whose filled entries point above the complete table.
structure WordArrayTablePrefix (mem : ByteArray) (ptr : UInt256)
    (groups : List (List UInt256)) (filled limit : Nat) : Prop where
  low : 96 ≤ ptr.toNat
  progress : filled ≤ groups.length
  span : ptr.toNat+32+32*groups.length ≤ limit
  covered : ptr.toNat+32+32*groups.length ≤ mem.size
  length : memLoad ptr mem = UInt256.ofNat groups.length
  arrays : ∀ i (hi : i < filled), ∃ p,
    memLoad (UInt256.ofNat (ptr.toNat+32+32*i)) mem = p ∧
    WordArrayMemoryView mem p groups[i] limit ∧ ptr.toNat+32+32*groups.length ≤ p.toNat

theorem WordArrayTablePrefix.preserve {mem after : ByteArray} {ptr : UInt256}
    {groups : List (List UInt256)} {filled limit next : Nat}
    (h : WordArrayTablePrefix mem ptr groups filled limit) (hp : MemoryPrefix mem after limit)
    (hn : limit ≤ next) (hb : next < UInt256.size) : WordArrayTablePrefix after ptr groups filled next := by
  have hs := h.span
  have hc := h.covered
  refine ⟨h.low,h.progress,by omega,le_trans h.covered hp.size,?_,?_⟩
  · exact (memLoad_of_prefix hp ptr h.low (by omega) (by omega)).trans h.length
  · intro i hi
    obtain ⟨p,hptr,hv,hlo⟩ := h.arrays i hi
    have hn' : (UInt256.ofNat (ptr.toNat+32+32*i)).toNat = ptr.toNat+32+32*i :=
      ulit_toNat' _ (by have := h.progress; omega)
    exact ⟨p,(memLoad_of_prefix hp _ (by rw [hn']; have := h.low; omega)
      (by rw [hn']; have := h.progress; omega) (by rw [hn']; have := h.progress; omega)).trans hptr,
      { hv.preserve hp (by omega) with span := le_trans hv.span hn },hlo⟩

theorem WordArrayTablePrefix.set {mem : ByteArray} {ptr p : UInt256}
    {groups : List (List UInt256)} {words : List UInt256} {filled limit : Nat}
    (h : WordArrayTablePrefix mem ptr groups filled limit) (hi : filled < groups.length)
    (hv : WordArrayMemoryView mem p words limit) (hlo : ptr.toNat+32+32*groups.length ≤ p.toNat)
    (hb : limit < UInt256.size) :
    WordArrayTablePrefix (Reasoning.Theory.writeWord mem (ptr.toNat+32+32*filled) p)
      ptr (groups.set filled words) (filled+1) limit := by
  have hs := h.span
  have hc := h.covered
  refine ⟨h.low,by rw [List.length_set]; omega,by simpa only [List.length_set] using h.span,?_,?_,?_⟩
  · rw [List.length_set,writeWord_sparse_size]; omega
  · rw [List.length_set]
    exact (memLoad_write_below _ _ _ _ (by omega) (by omega)).trans h.length
  · intro j hj
    have hslot : (UInt256.ofNat (ptr.toNat+32+32*j)).toNat = ptr.toNat+32+32*j := ulit_toNat' _ (by omega)
    by_cases he : j = filled
    · subst j
      rw [List.getElem_set_self,List.length_set]
      refine ⟨p,?_,hv.write_disjoint _ _ hb (Or.inr (by omega)),hlo⟩
      exact mloadWordValue_of_readWithPadding (by rw [hslot,writeWord_sparse_size]; omega)
        (by rw [hslot]; exact writeWord_sparse_read_back _ _ _)
    · simp only [List.getElem_set_ne (Ne.symm he),List.length_set]
      obtain ⟨q,hq,hv',hlo'⟩ := h.arrays j (by omega)
      exact ⟨q,(memLoad_write_below _ _ _ _ (by rw [hslot]; omega) (by rw [hslot]; omega)).trans hq,
        hv'.write_disjoint _ _ hb (Or.inr (by omega)),hlo'⟩

theorem WordArrayTablePrefix.finish {mem : ByteArray} {ptr : UInt256}
    {groups : List (List UInt256)} {limit : Nat}
    (h : WordArrayTablePrefix mem ptr groups groups.length limit) : WordArrayArrayMemoryView mem ptr groups limit :=
  ⟨h.low,h.span,h.covered,h.length,fun i hi => by obtain ⟨p,hp,hv,_⟩ := h.arrays i hi; exact ⟨p,hp,hv⟩⟩

theorem arrayTableAllocationMemory_view (mem : ByteArray) (heap : UInt256) (n : Nat)
    (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1) (hn : n ≤ 2^64-1) :
    let next := allocateNext heap.toNat (32+32*n)
    let final := arrayTableAllocationMemory mem heap n
    MemoryPrefix mem final heap.toNat ∧
      WordArrayTablePrefix final heap (List.replicate n []) 0 next ∧
      memLoad (UInt256.ofNat 64) final = UInt256.ofNat next := by
  dsimp only
  let header := arrayAllocationHeaderMemory mem heap n
  have hc : heap.toNat+32 ≤ header.size := by
    dsimp only [header,arrayAllocationHeaderMemory]; rw [writeWord_sparse_size]; omega
  have hp1 : MemoryPrefix mem header heap.toNat :=
    (memoryPrefix_sparse_writeWord mem 64 _ _ (Or.inr (by decide))).trans
      (memoryPrefix_sparse_writeWord _ heap.toNat _ _ (Or.inl (le_refl _)))
  have hp2 := writeWordSequence_prefix header (heap.toNat+32) (heap.toNat+32)
    (List.replicate n (UInt256.ofNat 96)) (le_refl _)
  have hlen : memLoad heap header = UInt256.ofNat n :=
    mloadWordValue_of_readWithPadding (by omega) (writeWord_sparse_read_back _ _ _)
  have hcover : heap.toNat+32+32*n ≤ (arrayTableAllocationMemory mem heap n).size := by
    by_cases hz : n=0
    · subst n; simpa only [arrayTableAllocationMemory,List.replicate_zero,writeWordSequence,Nat.mul_zero,Nat.add_zero] using hc
    · have h := writeWordSequence_covers header (heap.toNat+32) (List.replicate n (UInt256.ofNat 96))
        (by intro he; have hh := congrArg List.length he; simp only [List.length_replicate,List.length_nil] at hh; contradiction)
      simpa only [List.length_replicate] using h
  refine ⟨hp1.trans (hp2.mono (by omega)),⟨hlo,by simp only [List.length_replicate]; omega,?_,?_,?_,by intros; contradiction⟩,?_⟩
  · rw [List.length_replicate,allocateNext_wordArray hh hn]
  · simpa only [List.length_replicate] using hcover
  · rw [List.length_replicate]
    exact (memLoad_of_prefix hp2 heap hlo (le_refl _) hc).trans hlen
  · apply mloadWordValue_of_readWithPadding
    · change 64 < (arrayTableAllocationMemory mem heap n).size; omega
    · change (writeWordSequence header (heap.toNat+32) (List.replicate n (UInt256.ofNat 96))).readWithPadding 64 32 = _
      rw [writeWordSequence_read_below _ _ _ _ (by omega) (by omega)]
      dsimp only [header,arrayAllocationHeaderMemory]
      rw [writeWord_sparse_read_preserved _ _ 64 _ (Or.inl ⟨hlo,by rw [writeWord_sparse_size]; omega⟩),writeWord_sparse_read_back]

end Benchmarks.EAS.EAS
