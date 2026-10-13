import Benchmarks.EAS.EAS.MemoryCopy
import Benchmarks.EAS.EAS.ByteViews
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: sequential word reads and their byte view.
def memoryWords (mem : ByteArray) (off : Nat) : Nat → List UInt256
  | 0 => []
  | n + 1 => memLoad (UInt256.ofNat off) mem :: memoryWords mem (off + 32) n

theorem memoryWords_length (mem : ByteArray) (off n : Nat) : (memoryWords mem off n).length = n := by
  induction n generalizing off with
  | zero => rfl
  | succ n ih => simp only [memoryWords, List.length_cons, ih]

theorem memLoad_bytes (mem : ByteArray) (off : Nat)
    (hbound : off < UInt256.size) (hin : off + 32 ≤ mem.size) :
    (memLoad (UInt256.ofNat off) mem).toByteArray = mem.readWithPadding off 32 := by
  change (if (UInt256.ofNat off).toNat ≥ mem.size then (⟨0⟩ : UInt256)
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding (UInt256.ofNat off).toNat 32))).toByteArray = _
  rw [ulit_toNat' _ hbound, if_neg (by omega)]
  exact toByteArray_ofNat_fromByteArrayBigEndian_of_size
    (by rw [readWithPadding_eq_extract _ _ hin, ByteArray.size_extract]; omega)

theorem memoryWords_bytes (mem : ByteArray) (off n : Nat)
    (hbound : off + 32*n < UInt256.size) (hin : off + 32*n ≤ mem.size) :
    wordBytes (memoryWords mem off n) = mem.readWithPadding off (32*n) := by
  induction n generalizing off with
  | zero => simp only [memoryWords, wordBytes, Nat.mul_zero, byteArray_readWithPadding_zero]
  | succ n ih =>
    rw [memoryWords, wordBytes, memLoad_bytes _ _ (by omega) (by omega), ih _ (by omega) (by omega)]
    by_cases hz : n = 0
    · subst n
      simp only [Nat.mul_zero, Nat.mul_one, byteArray_readWithPadding_zero, ByteArray.append_empty]
    · rw [show 32*(n+1) = 32+32*n by omega,
        byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by omega) (by omega)]

theorem memoryWords_prefix {before after : ByteArray} {limit : Nat}
    (hp : MemoryPrefix before after limit) (off n : Nat) (hlo : 96 ≤ off)
    (hhi : off + 32*n ≤ limit) (hin : off + 32*n ≤ before.size)
    (hbound : off + 32*n < UInt256.size) :
    memoryWords after off n = memoryWords before off n := by
  induction n generalizing off with
  | zero => rfl
  | succ n ih =>
    rw [memoryWords, memoryWords, ih _ (by omega) (by omega) (by omega) (by omega)]
    congr 1
    change (if (UInt256.ofNat off).toNat ≥ after.size then (⟨0⟩ : UInt256)
      else UInt256.ofNat (fromByteArrayBigEndian (after.readWithPadding (UInt256.ofNat off).toNat 32))) =
      (if (UInt256.ofNat off).toNat ≥ before.size then (⟨0⟩ : UInt256)
      else UInt256.ofNat (fromByteArrayBigEndian (before.readWithPadding (UInt256.ofNat off).toNat 32)))
    rw [ulit_toNat' _ (by omega), if_neg (by have hg := hp.size; omega), if_neg (by omega),
      hp.read _ hlo (by omega) (by omega)]


-- LIBRARY CANDIDATE: a forward copy into disjoint memory equals a contiguous word write.
theorem easCopyWords_eq_sequence (src dst : UInt256) (mem : ByteArray) (i n : Nat)
    (hlo : 96 ≤ src.toNat + i) (hdisj : src.toNat + i + 32*n ≤ dst.toNat + i)
    (hin : src.toNat + i + 32*n ≤ mem.size) (hbound : dst.toNat + i + 32*n < UInt256.size) :
    easCopyWords src dst mem i n =
      writeWordSequence mem (dst.toNat + i) (memoryWords mem (src.toNat + i) n) := by
  induction n generalizing mem i with
  | zero => rfl
  | succ n ih =>
    have hd : (UInt256.ofNat i + dst).toNat = dst.toNat + i := by
      rw [u256_add_comm]
      exact uadd_word_ofNat_toNat dst i (by omega)
    have hs : UInt256.ofNat i + src = UInt256.ofNat (src.toNat + i) := by
      rw [u256_add_comm]
      apply u256_inj
      rw [uadd_word_ofNat_toNat src i (by omega), ulit_toNat' _ (by omega)]
    rw [easCopyWords, hd, hs, memoryWords, writeWordSequence]
    rw [ih _ (i+32) (by omega) (by omega) (by rw [writeWord_sparse_size]; omega) (by omega)]
    rw [memoryWords_prefix
      (memoryPrefix_sparse_writeWord mem (dst.toNat+i) (dst.toNat+i)
        (memLoad (UInt256.ofNat (src.toNat+i)) mem) (Or.inl (le_refl _)))
      (src.toNat+(i+32)) n (by omega) (by omega) (by omega) (by omega)]
    simp only [Nat.add_assoc]

end Benchmarks.EAS.EAS
