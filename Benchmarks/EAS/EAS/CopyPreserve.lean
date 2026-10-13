import Benchmarks.EAS.EAS.CopyEncodeViews
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: a word-copy loop preserves every initialized window below its destination.
theorem easCopyWords_preserveRead (src dst : UInt256) (mem : ByteArray) (i n read len : Nat)
    (hb : dst.toNat+i+32*n < UInt256.size) (hlo : read+len ≤ dst.toNat+i) (hin : read+len ≤ mem.size) :
    (easCopyWords src dst mem i n).readWithPadding read len = mem.readWithPadding read len := by
  induction n generalizing mem i with
  | zero => rfl
  | succ n ih =>
    have hd : (UInt256.ofNat i+dst).toNat = dst.toNat+i := by
      rw [u256_add_comm]
      exact uadd_word_ofNat_toNat dst i (by omega)
    rw [easCopyWords, ih _ (i+32) (by omega) (by omega) (by rw [writeWord_sparse_size]; omega), hd]
    exact writeWord_read_below_len mem (dst.toNat+i) read len _ hlo hin

theorem easCopyWords_size (src dst : UInt256) (mem : ByteArray) (i n : Nat) :
    mem.size ≤ (easCopyWords src dst mem i n).size := by
  induction n generalizing mem i with
  | zero => exact le_refl _
  | succ n ih =>
    exact le_trans (by rw [writeWord_sparse_size]; exact Nat.le_max_left _ _)
      (ih _ (i+32))

theorem easCopyWords_prefix (src dst : UInt256) (mem : ByteArray) (i n limit : Nat)
    (hb : dst.toNat+i+32*n < UInt256.size) (hlo : limit ≤ dst.toNat+i) :
    MemoryPrefix mem (easCopyWords src dst mem i n) limit := by
  refine ⟨easCopyWords_size src dst mem i n, ?_⟩
  intro off _ hhi hin
  exact easCopyWords_preserveRead src dst mem i n off 32 hb (by omega) hin

end Benchmarks.EAS.EAS
