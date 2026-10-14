import Benchmarks.EAS.EAS.OneRevocationResult
import Benchmarks.EAS.EAS.RevokeCalldataCopy
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def delegatedRevokeCopiedMemory (mem : ByteArray) (heap : UInt256) (cd : ByteArray) : ByteArray :=
  revocationRecordMemory (oneRevocationArrayMemory mem heap) (UInt256.ofNat (heap.toNat+128)) (revocationDataRecord cd 36)
def delegatedRevokeTailMemory (mem : ByteArray) (heap : UInt256) (cd : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord (delegatedRevokeCopiedMemory mem heap cd) (heap.toNat+32) (UInt256.ofNat (heap.toNat+128))

theorem delegatedRevokeCopiedMemory_facts (mem : ByteArray) (heap : UInt256) (cd : ByteArray)
    (hlo : 128 ≤ heap.toNat) (hb : heap.toNat+192 < UInt256.size) :
    heap.toNat+192 ≤ (delegatedRevokeCopiedMemory mem heap cd).size ∧
    memLoad heap (delegatedRevokeCopiedMemory mem heap cd) = ⟨1⟩ ∧
    memLoad (UInt256.ofNat 64) (delegatedRevokeCopiedMemory mem heap cd) = UInt256.ofNat (heap.toNat+192) ∧
    RevocationRequestMemoryView (delegatedRevokeCopiedMemory mem heap cd)
      (UInt256.ofNat (heap.toNat+128)) (revocationDataRecord cd 36) ∧
    MemoryPrefix mem (delegatedRevokeCopiedMemory mem heap cd) heap.toNat := by
  have hn : (UInt256.ofNat (heap.toNat+128)).toNat = heap.toNat+128 := ulit_toNat' _ (by omega)
  have hf := oneRevocationArrayMemory_views mem heap (by omega)
  have hc := revocationRecordMemory_facts (oneRevocationArrayMemory mem heap) (UInt256.ofNat (heap.toNat+128))
    (revocationDataRecord cd 36) (by rw [hn]; omega) (by rw [hn]; omega)
  simp only [hn,show heap.toNat+128+64 = heap.toNat+192 by omega] at hc
  refine ⟨?_,?_,hc.2.2,hc.2.1,hf.1.trans (hc.1.mono (by omega))⟩
  · have hh := hc.2.1.covered
    rw [hn] at hh
    change heap.toNat+128+64 ≤ (delegatedRevokeCopiedMemory mem heap cd).size at hh
    omega
  · exact (memLoad_of_prefix hc.1 heap (by omega) (by omega) (by have := hf.2.1; omega)).trans hf.2.2.2

theorem delegatedRevokeTailMemory_facts (mem : ByteArray) (heap : UInt256) (cd : ByteArray)
    (hlo : 128 ≤ heap.toNat) (hb : heap.toNat+192 < UInt256.size)
    (hcover : 128 ≤ mem.size) (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩) :
    RevocationRequestArrayMemoryView (delegatedRevokeTailMemory mem heap cd) heap [revocationDataRecord cd 36] (heap.toNat+192) ∧
    memLoad (UInt256.ofNat 64) (delegatedRevokeTailMemory mem heap cd) = UInt256.ofNat (heap.toNat+192) ∧
    memLoad (UInt256.ofNat 96) (delegatedRevokeTailMemory mem heap cd) = ⟨0⟩ ∧
    MemoryPrefix mem (delegatedRevokeTailMemory mem heap cd) heap.toNat := by
  have hc := delegatedRevokeCopiedMemory_facts mem heap cd hlo hb
  have hn : (UInt256.ofNat (heap.toNat+128)).toNat = heap.toNat+128 := ulit_toNat' _ (by omega)
  have hp := memoryPrefix_sparse_writeWord (delegatedRevokeCopiedMemory mem heap cd) (heap.toNat+32) heap.toNat
    (UInt256.ofNat (heap.toNat+128)) (Or.inl (by omega))
  have htotal : MemoryPrefix mem (delegatedRevokeTailMemory mem heap cd) heap.toNat := hc.2.2.2.2.trans hp
  refine ⟨⟨by omega,by simp only [List.length_singleton]; omega,?_,?_,?_⟩,?_,?_,htotal⟩
  · have := hp.size
    simp only [List.length_singleton]
    change _ ≤ (Reasoning.Theory.writeWord _ _ _).size
    rw [writeWord_sparse_size]
    omega
  · exact (memLoad_write_below _ _ _ _ (le_refl _) (by have := hc.1; omega)).trans hc.2.1
  · intro i hi
    have hiz : i = 0 := by simp only [List.length_singleton] at hi; omega
    subst i
    refine ⟨UInt256.ofNat (heap.toNat+128),?_,?_,by simpa only [hn,Nat.add_assoc,Nat.reduceAdd] using (le_refl (heap.toNat+192))⟩
    · simp only [Nat.mul_zero,Nat.add_zero]
      apply mloadWordValue_of_readWithPadding
      · rw [ulit_toNat' _ (by omega)]
        change _ < (Reasoning.Theory.writeWord _ _ _).size
        rw [writeWord_sparse_size]; omega
      · rw [ulit_toNat' _ (by omega)]; exact writeWord_sparse_read_back _ _ _
    · exact hc.2.2.2.1.write_below (heap.toNat+32) _ (by rw [hn]; omega) (by rw [hn]; omega)
  · exact (memLoad_write_below _ _ _ _ (by change 96 ≤ _; omega) (by change 96 ≤ _; have := hc.1; omega)).trans hc.2.2.1
  · exact (memLoad_of_prefix htotal (UInt256.ofNat 96) (by decide) (by change 128 ≤ _; omega) hcover).trans hzero

end Benchmarks.EAS.EAS
