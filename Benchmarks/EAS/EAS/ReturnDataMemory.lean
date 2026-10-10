import Benchmarks.EAS.EAS.CopyEncodeViews
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: allocating and copying a byte-array return buffer preserves older memory.
def bytesReturnMemory (mem : ByteArray) (ptr : UInt256) (heap : Nat) (out : ByteArray) : ByteArray :=
  out.write 0 (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat heap))
    ptr.toNat (UInt256.ofNat out.size)) (ptr.toNat+32) out.size

theorem bytesReturnMemory_prefix (mem : ByteArray) (ptr : UInt256) (heap : Nat) (out : ByteArray) :
    MemoryPrefix mem (bytesReturnMemory mem ptr heap out) ptr.toNat := by
  have hp := (memoryPrefix_sparse_writeWord mem 64 ptr.toNat (UInt256.ofNat heap) (Or.inr (by decide))).trans
    (memoryPrefix_sparse_writeWord _ ptr.toNat ptr.toNat (UInt256.ofNat out.size) (Or.inl (le_refl _)))
  apply hp.trans
  refine ⟨byteArray_write_size_ge_base _ _ _ _ _, ?_⟩
  intro off hlo hhi hin
  by_cases hz : out.size = 0
  · simp only [bytesReturnMemory, hz, byteArray_write_len_zero]
  · exact write_read_below_gen_extend out _ (ptr.toNat+32) out.size off hz (le_refl _)
      (by rw [writeWord_sparse_size]; omega) (by omega)

theorem bytesReturnMemory_heap (mem : ByteArray) (ptr : UInt256) (heap : Nat) (out : ByteArray)
    (hlo : 96 ≤ ptr.toNat) :
    memLoad (UInt256.ofNat 64) (bytesReturnMemory mem ptr heap out) = UInt256.ofNat heap := by
  let inner := Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat heap))
    ptr.toNat (UInt256.ofNat out.size)
  have hs : 96 ≤ inner.size := by simp only [inner, writeWord_sparse_size]; omega
  apply mloadWordValue_of_readWithPadding
  · change 64 < (bytesReturnMemory mem ptr heap out).size
    have h := byteArray_write_size_ge_base out inner 0 (ptr.toNat+32) out.size
    exact lt_of_lt_of_le (by omega) h
  · change (out.write 0 inner (ptr.toNat+32) out.size).readWithPadding 64 32 = _
    have hr : (out.write 0 inner (ptr.toNat+32) out.size).readWithPadding 64 32 = inner.readWithPadding 64 32 := by
      by_cases hz : out.size = 0
      · simp only [hz, byteArray_write_len_zero]
      · exact write_read_below_gen_extend out inner (ptr.toNat+32) out.size 64 hz (le_refl _)
          (by simp only [inner, writeWord_sparse_size]; omega) (by omega)
    rw [hr]
    dsimp only [inner]
    rw [writeWord_read_below_len _ _ 64 32 _ hlo
      (by rw [writeWord_sparse_size]; omega), writeWord_sparse_read_back]

end Benchmarks.EAS.EAS
