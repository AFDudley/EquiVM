import Benchmarks.EAS.EAS.Allocate
import Benchmarks.EAS.EAS.RecordCreateMemory
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- The first record write makes the reserved, implicitly zero-filled array payload explicit.
def recordPadding (mem : ByteArray) (heap : Nat) : ByteArray :=
  Reasoning.Theory.writeWord
    (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap 320))) heap ⟨0⟩

theorem recordPadding_prefix (mem : ByteArray) (heap : Nat) :
    MemoryPrefix mem (recordPadding mem heap) heap :=
  (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inr (by decide))).trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (le_refl _)))

theorem recordPadding_covers (mem : ByteArray) (heap : Nat) :
    heap+32 ≤ (recordPadding mem heap).size := by
  unfold recordPadding
  rw [writeWord_sparse_size]
  exact Nat.le_max_right _ _

theorem recordCreateMemory_padding_prefix (mem : ByteArray) (heap dataPtr : UInt256)
    (a : AttestationRecord) (hu : a.uid = ⟨0⟩) :
    MemoryPrefix (recordPadding mem heap.toNat)
      (recordCreateMemory
        (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat 320))) heap dataPtr a)
      heap.toNat := by
  unfold recordPadding
  simp only [recordCreateMemory,AttestationRecord.words,List.cons_append,List.nil_append,hu]
  rw [writeWordSequence]
  exact writeWordSequence_prefix _ (heap.toNat+32) heap.toNat _ (by omega)

end Benchmarks.EAS.EAS
