import Benchmarks.EAS.EAS.ReservePrefix
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: scratch writes below 96 preserve the reserved allocation prefix, including implicit zeroes.
theorem recordPadding_low_write (mem : ByteArray) (heap off : Nat) (word : UInt256)
    (hmem : 96 ≤ mem.size) (hoff : off+32 ≤ 96) :
    MemoryPrefix (recordPadding mem heap) (recordPadding (Reasoning.Theory.writeWord mem off word) heap) heap := by
  let free := UInt256.ofNat (allocateNext heap 320)
  have hlow : (Reasoning.Theory.writeWord mem off word).size = mem.size := by rw [writeWord_sparse_size]; omega
  have ha : (Reasoning.Theory.writeWord mem 64 free).size = mem.size := by rw [writeWord_sparse_size]; omega
  have hb : (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem off word) 64 free).size = mem.size := by
    rw [writeWord_sparse_size,hlow]; omega
  refine ⟨by simp only [recordPadding,writeWord_sparse_size]; omega,fun read hlo hhi hin => ?_⟩
  change (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem off word) 64 free) heap ⟨0⟩).readWithPadding read 32 =
    (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem 64 free) heap ⟨0⟩).readWithPadding read 32
  by_cases hm : heap ≤ mem.size
  · rw [writeWord_sparse_read_preserved _ heap read ⟨0⟩ (Or.inl ⟨hhi,by rw [hb]; omega⟩),
      writeWord_sparse_read_preserved _ heap read ⟨0⟩ (Or.inl ⟨hhi,by rw [ha]; omega⟩),
      writeWord_sparse_read_preserved _ 64 read free (Or.inr ⟨hlo,by rw [hlow]; omega⟩),
      writeWord_sparse_read_preserved _ 64 read free (Or.inr ⟨hlo,by omega⟩),
      writeWord_sparse_read_preserved _ off read word (Or.inr ⟨by omega,by omega⟩)]
  · have hp : (mem++ByteArray.zeroes (heap-mem.size)).size = heap := by
      rw [ByteArray.size_append,ByteArray_zeroes_size]; omega
    have hread (m : ByteArray) (he : m.size = mem.size) :
        (Reasoning.Theory.writeWord m heap ⟨0⟩).readWithPadding read 32 =
        (m++ByteArray.zeroes (heap-mem.size)).readWithPadding read 32 := by
      have hs : (m++ByteArray.zeroes (heap-mem.size)).size = heap := by
        rw [ByteArray.size_append,ByteArray_zeroes_size,he]; omega
      rw [writeWord_sparse_eq _ _ _ (by rw [he]; omega),he,
        readWithPadding_eq_extract _ read (by rw [ByteArray.size_append,hs,toByteArray_size]; omega),
        extract_append_left _ _ _ _ (by rw [hs]; exact hhi),
        ← readWithPadding_eq_extract _ read (by rw [hs]; exact hhi)]
    rw [hread _ hb,hread _ ha,
      ← writeWord_append_suffix (Reasoning.Theory.writeWord mem off word) _ 64 free (by rw [hlow]; exact hmem),
      ← writeWord_append_suffix mem _ off word (by omega),
      ← writeWord_append_suffix mem _ 64 free hmem,
      writeWord_sparse_read_preserved _ 64 read free (Or.inr ⟨hlo,by rw [writeWord_sparse_size,hp]; omega⟩),
      writeWord_sparse_read_preserved _ 64 read free (Or.inr ⟨hlo,by rw [hp]; exact hhi⟩),
      writeWord_sparse_read_preserved _ off read word (Or.inr ⟨by omega,by rw [hp]; exact hhi⟩)]

theorem recordPadding_hash_prefix (mem : ByteArray) (heap : Nat) (word : UInt256) (hmem : 96 ≤ mem.size) :
    MemoryPrefix (recordPadding mem heap) (recordPadding (twoWordHashMem word ⟨1⟩ mem) heap) heap :=
  (recordPadding_low_write mem heap 0 word hmem (by decide)).trans
    (recordPadding_low_write _ heap 32 ⟨1⟩ (by rw [writeWord_sparse_size]; omega) (by decide))

end Benchmarks.EAS.EAS
