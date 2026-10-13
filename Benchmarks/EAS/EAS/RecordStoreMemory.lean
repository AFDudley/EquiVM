import Benchmarks.EAS.EAS.RecordUID
import Benchmarks.EAS.EAS.GetAttestationEVM
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def recordStoreMemory (mem : ByteArray) (src word : UInt256) : ByteArray :=
  twoWordHashMem word ⟨1⟩ (Reasoning.Theory.writeWord mem src.toNat word)

theorem recordStoreMemory_prefix (mem : ByteArray) (src word : UInt256) :
    MemoryPrefix mem (recordStoreMemory mem src word) src.toNat :=
  (memoryPrefix_sparse_writeWord mem src.toNat src.toNat word (Or.inl (le_refl _))).trans
    ((memoryPrefix_sparse_writeWord _ 0 src.toNat word (Or.inr (by decide))).trans
      (memoryPrefix_sparse_writeWord _ 32 src.toNat (⟨1⟩ : UInt256) (Or.inr (by decide))))

theorem recordStoreMemory_view {mem : ByteArray} {src dataPtr : UInt256} {a : AttestationRecord}
    (h : AttestationMemoryView mem src dataPtr a) (word : UInt256)
    (hdata : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ src.toNat) (hb : src.toNat+320 < UInt256.size) :
    AttestationMemoryView (recordStoreMemory mem src word) src dataPtr {a with uid := word} := by
  have hv := h.setUID word hdata hb
  have hp : MemoryPrefix (Reasoning.Theory.writeWord mem src.toNat word) (recordStoreMemory mem src word) (src.toNat+320) :=
    (memoryPrefix_sparse_writeWord _ 0 (src.toNat+320) word (Or.inr (by decide))).trans
      (memoryPrefix_sparse_writeWord _ 32 (src.toNat+320) (⟨1⟩ : UInt256) (Or.inr (by decide)))
  exact hv.preserve hp (le_refl _) (by exact le_trans hdata (Nat.le_add_right _ _)) hb

theorem recordStoreMemory_heap (mem : ByteArray) (src word heap : UInt256)
    (hlo : 96 ≤ src.toNat) (hin : 96 ≤ mem.size) (hh : memLoad (UInt256.ofNat 64) mem = heap) :
    memLoad (UInt256.ofNat 64) (recordStoreMemory mem src word) = heap := by
  apply twoWordHashMem_heap word ⟨1⟩ heap _ (by rw [writeWord_sparse_size]; omega)
  exact (memLoad_write_below mem src.toNat (UInt256.ofNat 64) word hlo hin).trans hh

theorem recordStoreMemory_hash (mem : ByteArray) (src word : UInt256) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (recordStoreMemory mem src word) = dbSlot word :=
  twoWordHashMem_solcMappingSlot_any ⟨1⟩ word _

end Benchmarks.EAS.EAS
