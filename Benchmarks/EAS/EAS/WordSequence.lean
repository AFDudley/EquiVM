import Benchmarks.EAS.EAS.Common
import Reasoning.HeapMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: contiguous word writes and their complete byte encoding.
def writeWordSequence (mem : ByteArray) (off : Nat) : List UInt256 → ByteArray
  | [] => mem
  | w :: ws => writeWordSequence (Reasoning.Theory.writeWord mem off w) (off + 32) ws

theorem writeWordSequence_grows (mem : ByteArray) (off : Nat) (ws : List UInt256) :
    mem.size ≤ (writeWordSequence mem off ws).size := by
  induction ws generalizing mem off with
  | nil => exact le_refl _
  | cons w ws ih =>
    exact le_trans (by rw [writeWord_sparse_size]; exact Nat.le_max_left _ _)
      (ih (Reasoning.Theory.writeWord mem off w) (off + 32))

theorem writeWordSequence_covers (mem : ByteArray) (off : Nat) (ws : List UInt256)
    (hne : ws ≠ []) : off + 32 * ws.length ≤ (writeWordSequence mem off ws).size := by
  induction ws generalizing mem off with
  | nil => contradiction
  | cons w ws ih =>
    cases ws with
    | nil => simp only [writeWordSequence, List.length_cons, List.length_nil, writeWord_sparse_size]; omega
    | cons x xs =>
      have h := ih (Reasoning.Theory.writeWord mem off w) (off + 32) (by simp)
      simp only [List.length_cons] at h ⊢
      exact le_trans (by omega) h

theorem writeWordSequence_read_below (mem : ByteArray) (off read : Nat) (ws : List UInt256)
    (hin : read + 32 ≤ mem.size) (hlo : read + 32 ≤ off) :
    (writeWordSequence mem off ws).readWithPadding read 32 = mem.readWithPadding read 32 := by
  induction ws generalizing mem off with
  | nil => rfl
  | cons w ws ih =>
    rw [writeWordSequence, ih _ _ (by rw [writeWord_sparse_size]; omega) (by omega)]
    exact writeWord_sparse_read_preserved mem off read w (Or.inl ⟨hlo, hin⟩)

theorem writeWordSequence_read (mem : ByteArray) (off : Nat) (ws : List UInt256) :
    (writeWordSequence mem off ws).readWithPadding off (32 * ws.length) = wordBytes ws := by
  induction ws generalizing mem off with
  | nil => exact byteArray_readWithPadding_zero _ _
  | cons w ws ih =>
    have hhead : (writeWordSequence mem off (w :: ws)).readWithPadding off 32 = w.toByteArray := by
      rw [writeWordSequence, writeWordSequence_read_below _ (off + 32) off ws
        (by rw [writeWord_sparse_size]; omega) (by omega), writeWord_sparse_read_back]
    cases ws with
    | nil => simpa only [wordBytes, ByteArray.append_empty] using hhead
    | cons x xs =>
      rw [show 32 * (w :: x :: xs).length = 32 + 32 * (x :: xs).length by simp <;> omega]
      rw [byteArray_readWithPadding_split_unbounded _ off 32 (32 * (x :: xs).length)
        (by decide) (by simp <;> omega) (by
          have h := writeWordSequence_covers mem off (w :: x :: xs) (by simp)
          simp only [List.length_cons] at h ⊢
          omega), hhead]
      change w.toByteArray ++ (writeWordSequence (Reasoning.Theory.writeWord mem off w) (off + 32) (x :: xs)).readWithPadding
        (off + 32) (32 * (x :: xs).length) = _
      rw [ih]
      rfl



-- LIBRARY CANDIDATE: allocating above the reserved memory preserves the new heap cursor.
theorem writeWordSequence_setFree_load64 (mem : ByteArray) (off : Nat) (ws : List UInt256)
    (heap : UInt256) (hlo : 96 ≤ off) :
    memLoad (UInt256.ofNat 64) (writeWordSequence (Reasoning.Theory.writeWord mem 64 heap) off ws) = heap := by
  apply mloadWordValue_of_readWithPadding
  · have hh := writeWordSequence_grows (Reasoning.Theory.writeWord mem 64 heap) off ws
    rw [writeWord_sparse_size] at hh
    change 64 < (writeWordSequence (Reasoning.Theory.writeWord mem 64 heap) off ws).size
    exact lt_of_lt_of_le (by omega) hh
  · change (writeWordSequence (Reasoning.Theory.writeWord mem 64 heap) off ws).readWithPadding 64 32 = _
    rw [writeWordSequence_read_below (Reasoning.Theory.writeWord mem 64 heap) off 64 ws
      (by rw [writeWord_sparse_size]; omega) hlo, writeWord_sparse_read_back]

-- LIBRARY CANDIDATE: read one word of a contiguous memory record.
theorem writeWordSequence_read_index (mem : ByteArray) (off : Nat) (ws : List UInt256)
    (i : Nat) (hi : i < ws.length) :
    (writeWordSequence mem off ws).readWithPadding (off + 32*i) 32 = ws[i].toByteArray := by
  induction ws generalizing mem off i with
  | nil => simp at hi
  | cons w ws ih =>
    cases i with
    | zero =>
      simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero, writeWordSequence]
      rw [writeWordSequence_read_below _ _ off _ (by rw [writeWord_sparse_size]; omega) (by omega), writeWord_sparse_read_back]
    | succ i =>
      have hi' : i < ws.length := by simpa using hi
      simpa only [writeWordSequence, List.getElem_cons_succ, Nat.mul_succ, Nat.add_assoc,
        show 32 + 32 * i = 32 * i + 32 by omega] using ih (Reasoning.Theory.writeWord mem off w) (off + 32) i hi'

-- LIBRARY CANDIDATE: contiguous writes preserve the allocated memory below their start.
theorem writeWordSequence_prefix (mem : ByteArray) (off limit : Nat) (ws : List UInt256)
    (hlo : limit ≤ off) : MemoryPrefix mem (writeWordSequence mem off ws) limit :=
  ⟨writeWordSequence_grows mem off ws,
    fun read _ hhi hin => writeWordSequence_read_below mem off read ws hin (le_trans hhi hlo)⟩

-- LIBRARY CANDIDATE: an in-bounds read of a memory word sequence.
theorem writeWordSequence_load_index (mem : ByteArray) (off : Nat) (ws : List UInt256)
    (i : Nat) (hi : i < ws.length) (hfit : off + 32*i < UInt256.size) :
    memLoad (UInt256.ofNat (off + 32*i)) (writeWordSequence mem off ws) = ws[i] := by
  have hcover := writeWordSequence_covers mem off ws (by intro hz; simp [hz] at hi)
  apply mloadWordValue_of_readWithPadding
  · rw [ulit_toNat' _ hfit]
    omega
  · rw [ulit_toNat' _ hfit]
    exact writeWordSequence_read_index mem off ws i hi

end Benchmarks.EAS.EAS
