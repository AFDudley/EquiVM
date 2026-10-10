import Benchmarks.EAS.EAS.RequestRegion
import Benchmarks.EAS.EAS.WordArrayAllocationView
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- GENERALIZES CopyRequestArrayMemory: parameterize the records and their bounded memory view.
structure PointerTablePrefix {α : Type} (view : ByteArray → UInt256 → α → Nat → Nat → Prop)
    (mem : ByteArray) (array : UInt256) (rs : List α) (i heap : Nat) : Prop where
  low : 96 ≤ array.toNat
  progress : i ≤ rs.length
  span : array.toNat+32+32*rs.length ≤ heap
  covered : array.toNat+32+32*i ≤ mem.size
  length : memLoad array mem = UInt256.ofNat rs.length
  elements : ∀ j (hj : j < i), ∃ ptr,
    memLoad (UInt256.ofNat (array.toNat+32+32*j)) mem = ptr ∧
    view mem ptr rs[j] (array.toNat+32+32*rs.length) heap

theorem PointerTablePrefix.preserve {α : Type} {view : ByteArray → UInt256 → α → Nat → Nat → Prop}
    {mem after : ByteArray} {array : UInt256} {rs : List α} {i heap next : Nat}
    (h : PointerTablePrefix view mem array rs i heap) (hp : MemoryPrefix mem after heap)
    (hn : heap ≤ next) (hb : next < UInt256.size)
    (hv : ∀ ptr r, view mem ptr r (array.toNat+32+32*rs.length) heap →
      view after ptr r (array.toNat+32+32*rs.length) next) :
    PointerTablePrefix view after array rs i next := by
  have hs := h.span
  have hc := h.covered
  have hi := h.progress
  refine ⟨h.low,h.progress,by omega,le_trans h.covered hp.size,?_,?_⟩
  · exact (memLoad_of_prefix hp _ h.low (by omega) (by omega)).trans h.length
  · intro j hj
    obtain ⟨ptr,hptr,hr⟩ := h.elements j hj
    have hslot : (UInt256.ofNat (array.toNat+32+32*j)).toNat = array.toNat+32+32*j := ulit_toNat' _ (by omega)
    exact ⟨ptr,(memLoad_of_prefix hp _ (by rw [hslot]; have := h.low; omega)
      (by rw [hslot]; omega) (by rw [hslot]; omega)).trans hptr,hv ptr rs[j] hr⟩

theorem PointerTablePrefix.set {α : Type} {view : ByteArray → UInt256 → α → Nat → Nat → Prop}
    {mem : ByteArray} {array ptr : UInt256} {rs : List α} {i heap : Nat}
    (h : PointerTablePrefix view mem array rs i heap) (hi : i < rs.length)
    (hv : view mem ptr rs[i] (array.toNat+32+32*rs.length) heap) (hb : heap < UInt256.size)
    (hw : ∀ p r, view mem p r (array.toNat+32+32*rs.length) heap →
      view (Reasoning.Theory.writeWord mem (array.toNat+32+32*i) ptr) p r (array.toNat+32+32*rs.length) heap) :
    PointerTablePrefix view (Reasoning.Theory.writeWord mem (array.toNat+32+32*i) ptr) array rs (i+1) heap := by
  let dst := array.toNat+32+32*i
  let final := Reasoning.Theory.writeWord mem dst ptr
  have hs := h.span
  have hc := h.covered
  have hdst : (UInt256.ofNat dst).toNat = dst := ulit_toNat' _ (by dsimp only [dst]; omega)
  have hptr : memLoad (UInt256.ofNat dst) final = ptr := by
    apply mloadWordValue_of_readWithPadding
    · rw [hdst]; change dst < (Reasoning.Theory.writeWord mem dst ptr).size
      rw [writeWord_sparse_size]; omega
    · rw [hdst]; exact writeWord_sparse_read_back _ _ _
  refine ⟨h.low,by omega,h.span,?_,?_,?_⟩
  · rw [writeWord_sparse_size]; omega
  · exact (memLoad_write_below mem dst array ptr (by dsimp only [dst]; omega) (by omega)).trans h.length
  · intro j hj
    by_cases hj' : j < i
    · obtain ⟨p,hp,hr⟩ := h.elements j hj'
      have hslot : (UInt256.ofNat (array.toNat+32+32*j)).toNat = array.toNat+32+32*j := ulit_toNat' _ (by omega)
      exact ⟨p,(memLoad_write_below mem dst _ ptr (by rw [hslot]; dsimp only [dst]; omega)
        (by rw [hslot]; omega)).trans hp,hw p rs[j] hr⟩
    · have hj0 : j = i := by omega
      subst j
      exact ⟨ptr,hptr,hw ptr rs[i] hv⟩

theorem pointerTablePrefix_init {α : Type} (view : ByteArray → UInt256 → α → Nat → Nat → Prop)
    (mem : ByteArray) (array : UInt256) (rs : List α)
    (hlo : 96 ≤ array.toNat) (hh : array.toNat ≤ 2^64-1) (hlen : rs.length ≤ 2^64-1) :
    let next := allocateNext array.toNat (32+32*rs.length)
    let final := arrayAllocationHeaderMemory mem array rs.length
    MemoryPrefix mem final array.toNat ∧ PointerTablePrefix view final array rs 0 next ∧
    memLoad (UInt256.ofNat 64) final = UInt256.ofNat next := by

  dsimp only
  have hp1 : MemoryPrefix mem (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext array.toNat (32+32*rs.length)))) array.toNat :=
    memoryPrefix_sparse_writeWord _ _ _ _ (Or.inr (by decide))
  have hp2 := memoryPrefix_sparse_writeWord
    (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext array.toNat (32+32*rs.length))))
    array.toNat array.toNat (UInt256.ofNat rs.length) (Or.inl (le_refl _))
  refine ⟨hp1.trans hp2,?_,?_⟩
  · refine ⟨hlo,Nat.zero_le _,?_,?_,?_,?_⟩
    · rw [allocateNext_wordArray hh hlen]
    · simp only [arrayAllocationHeaderMemory,writeWord_sparse_size,Nat.mul_zero,Nat.add_zero]; omega
    · apply mloadWordValue_of_readWithPadding
      · simp only [arrayAllocationHeaderMemory,writeWord_sparse_size]; omega
      · exact writeWord_sparse_read_back _ _ _
    · intro j hj
      omega
  · unfold arrayAllocationHeaderMemory
    rw [memLoad_write_below _ _ _ _ (by exact hlo) (by rw [writeWord_sparse_size]; change 96 ≤ _; omega)]
    apply mloadWordValue_of_readWithPadding
    · rw [writeWord_sparse_size]; change 64 < _; omega
    · exact writeWord_sparse_read_back _ _ _

end Benchmarks.EAS.EAS
