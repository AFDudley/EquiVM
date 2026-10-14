import Benchmarks.EAS.EAS.OneRequestAllocate
import Benchmarks.EAS.EAS.RecordUID
import Benchmarks.EAS.EAS.RequestRegion
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem oneRequestArrayMemory_views (mem : ByteArray) (heap : UInt256) (hlo : 96 ≤ heap.toNat) :
    MemoryPrefix mem (oneRequestArrayMemory mem heap) heap.toNat ∧
    heap.toNat+256 ≤ (oneRequestArrayMemory mem heap).size ∧
    memLoad (UInt256.ofNat 64) (oneRequestArrayMemory mem heap) = UInt256.ofNat (heap.toNat+256) ∧
    memLoad heap (oneRequestArrayMemory mem heap) = ⟨1⟩ := by
  let m1 := oneRequestHeadMemory mem heap
  let m2 := Reasoning.Theory.writeWord m1 64 (UInt256.ofNat (heap.toNat+256))
  let m3 := writeWordSequence m2 (heap.toNat+64) [⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨96⟩,⟨0⟩]
  let final := Reasoning.Theory.writeWord m3 (heap.toNat+32) (UInt256.ofNat (heap.toNat+64))
  have hp1 : MemoryPrefix mem m1 heap.toNat :=
    (memoryPrefix_sparse_writeWord mem 64 heap.toNat _ (Or.inr (by decide))).trans
      (memoryPrefix_sparse_writeWord _ heap.toNat heap.toNat _ (Or.inl (le_refl _)))
  have hp2 : MemoryPrefix m1 m2 heap.toNat := memoryPrefix_sparse_writeWord _ 64 _ _ (Or.inr (by decide))
  have hp3 : MemoryPrefix m2 m3 (heap.toNat+64) := writeWordSequence_prefix _ _ _ _ (le_refl _)
  have hp4 : MemoryPrefix m3 final (heap.toNat+32) := memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (le_refl _))
  have hc1 : heap.toNat+32 ≤ m1.size := by change _ ≤ (Reasoning.Theory.writeWord _ heap.toNat _).size; rw [writeWord_sparse_size]; omega
  have hc2 : heap.toNat+32 ≤ m2.size := le_trans hc1 hp2.size
  have hc3 : heap.toNat+256 ≤ m3.size := writeWordSequence_covers m2 (heap.toNat+64) [⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨96⟩,⟨0⟩] (by simp)
  have hc4 := le_trans hc3 hp4.size
  have hf3 : memLoad (UInt256.ofNat 64) m3 = UInt256.ofNat (heap.toNat+256) :=
    writeWordSequence_setFree_load64 m1 _ _ _ (by omega)
  have hl1 : memLoad heap m1 = ⟨1⟩ := mloadWordValue_of_readWithPadding (by omega) (writeWord_sparse_read_back _ _ _)
  have hl2 : memLoad heap m2 = ⟨1⟩ := (memLoad_write_above m1 64 heap _ hlo hc1).trans hl1
  have hl3 : memLoad heap m3 = ⟨1⟩ := (memLoad_of_prefix hp3 heap hlo (by omega) hc2).trans hl2
  refine ⟨hp1.trans (hp2.trans ((hp3.mono (by omega)).trans (hp4.mono (by omega)))),hc4,?_,?_⟩
  · exact (memLoad_write_below m3 (heap.toNat+32) (UInt256.ofNat 64) _
      (by change 96 ≤ heap.toNat+32; omega) (by change 96 ≤ m3.size; omega)).trans hf3
  · exact (memLoad_of_prefix hp4 heap hlo (le_refl _) (by omega)).trans hl3

-- Install one object in an initialized singleton pointer table.
theorem requestSingleton_set {mem : ByteArray} {array ptr dataPtr : UInt256}
    {r : AttestationRequestRecord} {lower upper : Nat}
    (hlo : 96 ≤ array.toNat) (hreg : lower ≤ array.toNat)
    (hspan : array.toNat+64 ≤ ptr.toNat) (hdata : array.toNat+64 ≤ dataPtr.toNat)
    (hcover : array.toNat+64 ≤ mem.size) (hlen : memLoad array mem = ⟨1⟩)
    (hv : AttestationRequestMemoryView mem ptr dataPtr r)
    (hp : ptr.toNat+192 ≤ upper) (hd : dataPtr.toNat+32+32*((r.data.size+31)/32) ≤ upper)
    (hb : upper < UInt256.size) :
    AttestationRequestArrayRegion (Reasoning.Theory.writeWord mem (array.toNat+32) ptr) array [r] lower upper := by
  let final := Reasoning.Theory.writeWord mem (array.toNat+32) ptr
  have hptr : memLoad (UInt256.ofNat (array.toNat+32)) final = ptr := by
    have hn : (UInt256.ofNat (array.toNat+32)).toNat = array.toNat+32 := ulit_toNat' _ (by omega)
    apply mloadWordValue_of_readWithPadding
    · rw [hn]; change _ < (Reasoning.Theory.writeWord mem (array.toNat+32) ptr).size
      rw [writeWord_sparse_size]; omega
    · rw [hn]; exact writeWord_sparse_read_back _ _ _
  have hv' := hv.write_below (array.toNat+32) ptr (by omega) (by omega) (by omega)
  refine ⟨⟨hlo,by simp only [List.length_singleton]; omega,?_,?_,?_⟩,hreg,?_⟩
  · simp only [List.length_singleton]
    change _ ≤ (Reasoning.Theory.writeWord mem (array.toNat+32) ptr).size
    rw [writeWord_sparse_size]; omega
  · exact (memLoad_write_below mem (array.toNat+32) array ptr (le_refl _) (by omega)).trans hlen
  · intro i hi
    have hi0 : i = 0 := by simp only [List.length_singleton] at hi; omega
    subst i
    exact ⟨ptr,dataPtr,hptr,hv',hp,hd⟩
  · intro i hi
    have hi0 : i = 0 := by simp only [List.length_singleton] at hi; omega
    subst i
    change lower ≤ (memLoad (UInt256.ofNat (array.toNat+32)) final).toNat ∧ _
    rw [hptr,hv'.pointer]
    constructor <;> omega

end Benchmarks.EAS.EAS
