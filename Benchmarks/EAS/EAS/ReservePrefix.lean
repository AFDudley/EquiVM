import Benchmarks.EAS.EAS.ZeroCopy
import Benchmarks.EAS.EAS.RecordPadding
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: any write at a reservation boundary realizes the implicit zero prefix.
theorem memoryPrefix_reserve_write (mem : ByteArray) (off : Nat) (free word : UInt256)
    (hmem : 96 ≤ mem.size) :
    MemoryPrefix (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem 64 free) off ⟨0⟩)
      (Reasoning.Theory.writeWord mem off word) off := by
  have hfs : (Reasoning.Theory.writeWord mem 64 free).size = mem.size := by
    rw [writeWord_sparse_size]; omega
  refine ⟨by simp only [writeWord_sparse_size]; omega,fun read hlo hhi _ => ?_⟩
  by_cases hin : off ≤ mem.size
  · rw [writeWord_sparse_read_preserved mem off read word (Or.inl ⟨hhi,by omega⟩),
      writeWord_sparse_read_preserved _ off read ⟨0⟩ (Or.inl ⟨hhi,by rw [hfs]; omega⟩),
      writeWord_sparse_read_preserved mem 64 read free (Or.inr ⟨hlo,by omega⟩)]
  · have happ (a b : ByteArray) (hc : read+32 ≤ a.size) :
        (a++b).readWithPadding read 32 = a.readWithPadding read 32 := by
      rw [readWithPadding_eq_extract _ read (by rw [ByteArray.size_append]; omega),
        extract_append_left _ _ _ _ hc,← readWithPadding_eq_extract _ read hc]
    have hs : (mem++ByteArray.zeroes (off-mem.size)).size = off := by
      rw [ByteArray.size_append,ByteArray_zeroes_size]; omega
    rw [writeWord_sparse_eq mem off word (by omega),
      writeWord_sparse_eq (Reasoning.Theory.writeWord mem 64 free) off ⟨0⟩ (by rw [hfs]; omega),hfs,
      ← writeWord_append_suffix mem (ByteArray.zeroes (off-mem.size)) 64 free hmem,
      happ (mem++ByteArray.zeroes (off-mem.size)) word.toByteArray (by rw [hs]; exact hhi),
      happ (Reasoning.Theory.writeWord (mem++ByteArray.zeroes (off-mem.size)) 64 free) (⟨0⟩ : UInt256).toByteArray
        (by rw [writeWord_sparse_size,hs]; omega),
      writeWord_sparse_read_preserved _ 64 read free (Or.inr ⟨hlo,by rw [hs]; exact hhi⟩)]

theorem recordPadding_write_prefix (mem : ByteArray) (heap : Nat) (word : UInt256)
    (hmem : 96 ≤ mem.size) :
    MemoryPrefix (recordPadding mem heap) (Reasoning.Theory.writeWord mem heap word) heap :=
  memoryPrefix_reserve_write mem heap _ word hmem

end Benchmarks.EAS.EAS
