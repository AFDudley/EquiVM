import Benchmarks.EAS.EAS.RecordArrayViews
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: append the high bytes of a word to an initialized memory window.
theorem writeWord_append_read (mem : ByteArray) (off len take : Nat) (w : UInt256)
    (hin : off+len ≤ mem.size) (hp : 0 < take) (ht : take ≤ 32) :
    (Reasoning.Theory.writeWord mem (off+len) w).readWithPadding off (len+take) =
      mem.readWithPadding off len ++ w.toByteArray.extract 0 take := by
  have hw := writeWord_sparse_read_window mem (off+len) 0 take w (by omega) hp (by omega)
  simp only [Nat.add_zero,Nat.zero_add] at hw
  by_cases hz : len = 0
  · subst len
    simpa only [Nat.zero_add,Nat.add_zero,byteArray_readWithPadding_zero,ByteArray.empty_append] using hw
  rw [byteArray_readWithPadding_split_unbounded _ off len take (by omega) hp
    (by rw [writeWord_sparse_size]; omega),
    writeWord_read_below_len _ _ _ _ _ (le_refl _) hin,hw]

end Benchmarks.EAS.EAS
