import Benchmarks.EAS.EAS.ArrayDisjoint
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

structure AttestResultMemoryView (mem : ByteArray) (ptr uidPtr : UInt256)
    (uids : List UInt256) (used : UInt256) (heap : Nat) : Prop where
  low : 96 ≤ ptr.toNat
  span : ptr.toNat+64 ≤ uidPtr.toNat
  covered : ptr.toNat+64 ≤ mem.size
  usedValue : memLoad ptr mem = used
  uidPointer : memLoad (ptr+UInt256.ofNat 32) mem = uidPtr
  uids : WordArrayMemoryView mem uidPtr uids heap

theorem attestResultMemory_store {mem : ByteArray} {ptr uidPtr : UInt256} {uids : List UInt256}
    {heap : Nat} (used : UInt256) (hlo : 96 ≤ ptr.toNat) (hspan : ptr.toNat+64 ≤ uidPtr.toNat)
    (hin : ptr.toNat+64 ≤ mem.size) (hp : memLoad (ptr+UInt256.ofNat 32) mem = uidPtr)
    (hu : WordArrayMemoryView mem uidPtr uids heap) (hb : heap < UInt256.size) :
    AttestResultMemoryView (Reasoning.Theory.writeWord mem ptr.toNat used) ptr uidPtr uids used heap := by
  have he := hu.span
  have hn : (ptr+UInt256.ofNat 32).toNat = ptr.toNat+32 := uadd_word_ofNat_toNat _ _ (by omega)
  refine ⟨hlo,hspan,?_,?_,?_,hu.write_disjoint _ _ hb (Or.inr (by omega))⟩
  · rw [writeWord_sparse_size]; omega
  · exact mloadWordValue_of_readWithPadding (by rw [writeWord_sparse_size]; omega) (writeWord_sparse_read_back _ _ _)
  · exact (memLoad_write_above mem ptr.toNat (ptr+UInt256.ofNat 32) used (by rw [hn])
      (by rw [hn]; omega)).trans hp

theorem AttestResultMemoryView.preserve {before after : ByteArray} {ptr uidPtr : UInt256}
    {uids : List UInt256} {used : UInt256} {heap : Nat}
    (h : AttestResultMemoryView before ptr uidPtr uids used heap)
    (hp : MemoryPrefix before after heap) (hb : heap < UInt256.size) :
    AttestResultMemoryView after ptr uidPtr uids used heap := by
  have he := h.uids.span
  have hr := h.span
  have hn : (ptr+UInt256.ofNat 32).toNat = ptr.toNat+32 := uadd_word_ofNat_toNat _ _ (by omega)
  refine ⟨h.low,h.span,le_trans h.covered hp.size,?_,?_,h.uids.preserve hp hb⟩
  · exact (memLoad_of_prefix hp ptr h.low (by omega) (by have := h.covered; omega)).trans h.usedValue
  · exact (memLoad_of_prefix hp _ (by rw [hn]; have := h.low; omega) (by rw [hn]; omega)
      (by rw [hn]; have := h.covered; omega)).trans h.uidPointer

end Benchmarks.EAS.EAS
