import Benchmarks.Morpho.MetaMorphoV1_1.BytesArrayEncodeRead

/-! The two result headers and size bounds for returning all multicall results. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def multicallReturnStart (mem : ByteArray) (origin n : Nat) : ByteArray :=
  writeWord (writeWord mem origin ⟨32⟩) (origin + 32) (UInt256.ofNat n)

theorem multicallReturnStart_size (mem : ByteArray) (origin n : Nat) :
    (multicallReturnStart mem origin n).size = max mem.size (origin + 64) := by
  simp only [multicallReturnStart, writeWord_sparse_size]
  omega

theorem multicallReturnStart_prefix (mem : ByteArray) (origin n : Nat) :
    ByteMemoryPrefix mem (multicallReturnStart mem origin n) origin :=
  (byteMemoryPrefix_writeWord mem origin origin _ (.inl (le_refl _))).trans
    (byteMemoryPrefix_writeWord _ (origin + 32) origin _ (.inl (by omega)))

theorem multicallReturnStart_read (mem : ByteArray) (origin n : Nat) :
    (multicallReturnStart mem origin n).readWithPadding origin 64 =
      (⟨32⟩ : UInt256).toByteArray ++ (UInt256.ofNat n).toByteArray := by
  rw [show 64 = 32 + 32 from rfl,
    readWithPadding_split _ _ _ _ (by rw [multicallReturnStart_size]; omega)]
  simp only [multicallReturnStart]
  rw [writeWord_sparse_read_preserved_unbounded _ _ _ _ _
    (by rw [writeWord_sparse_size]; omega) (.inl (by omega)),
    writeWord_sparse_read_back, writeWord_sparse_read_back]

-- LIBRARY CANDIDATE: a bounded array of bounded byte strings fits in the EVM address space.
theorem bytesArrayTails_size_bound (bs : List ByteArray)
    (h : ∀ j (hj : j < bs.length), bs[j].size < 2 ^ 64) :
    (bytesArrayTails bs).size ≤ bs.length * (2 ^ 64 + 64) := by
  induction bs with
  | nil => simp only [bytesArrayTails, ByteArray.size_empty, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons b bs ih =>
      have hb := h 0 (by simp)
      simp only [List.getElem_cons_zero] at hb
      have hr : ∀ j (hj : j < bs.length), bs[j].size < 2 ^ 64 := by
        intro j hj
        simpa only [List.getElem_cons_succ] using h (j + 1) (by simp only [List.length_cons]; omega)
      have ht := ih hr
      rw [bytesArrayTails_size_cons, List.length_cons]
      have hp : paddedSize b.size ≤ b.size + 31 := by unfold paddedSize; omega
      omega

theorem MulticallMemory.returnBound {mem : ByteArray} {ptr : UInt256} {bs : List ByteArray}
    (h : MulticallMemory mem ptr bs) :
    ptr.toNat + 64 + 32 * bs.length + (bytesArrayTails bs).size + 32 < UInt256.size := by
  have ht := bytesArrayTails_size_bound bs (fun j hj ↦ by
    obtain ⟨p, _, _, hb, _, _⟩ := h.data j hj
    exact hb)
  have hp := h.bound
  have hn := h.lower
  change _ < 2 ^ 256
  omega

def multicallReturnMemory (mem : ByteArray) (origin : Nat) (bs : List ByteArray) : ByteArray :=
  bytesArrayEncodeMemory (multicallReturnStart mem origin bs.length) 160 (origin + 64)
    (origin + 64 + 32 * bs.length) origin bs

theorem multicallReturnMemory_read {mem : ByteArray} {ptr : UInt256} {bs : List ByteArray}
    (h : MulticallMemory mem ptr bs) :
    (multicallReturnMemory mem ptr.toNat bs).readWithPadding ptr.toNat
      (64 + 32 * bs.length + (bytesArrayTails bs).size) = bytesArrayReturnBytes bs := by
  have hb : ptr.toNat < UInt256.size := ptr.val.isLt
  have hs := h.sources.preserve hb (multicallReturnStart_prefix mem ptr.toNat bs.length)
  have hf := bytesArrayEncodeMemory_read (head := ptr.toNat + 64)
    (tail := ptr.toNat + 64 + 32 * bs.length) hs hb (by omega) (le_refl _) (by omega)
    (fun hn ↦ by rw [hn, List.length_nil, Nat.mul_zero, Nat.add_zero, multicallReturnStart_size]; omega)
    (origin := ptr.toNat)
  obtain ⟨hsize, hheads, htails⟩ := hf
  change ptr.toNat + 64 + 32 * bs.length + (bytesArrayTails bs).size ≤
    (multicallReturnMemory mem ptr.toNat bs).size at hsize
  change (multicallReturnMemory mem ptr.toNat bs).readWithPadding (ptr.toNat + 64)
    (32 * bs.length) = _ at hheads
  change (multicallReturnMemory mem ptr.toNat bs).readWithPadding (ptr.toNat + 64 + 32 * bs.length)
    (bytesArrayTails bs).size = _ at htails
  have hp := bytesArrayEncodeMemory_prefix (head := ptr.toNat + 64)
    (tail := ptr.toNat + 64 + 32 * bs.length) hs hb (by omega) (le_refl _) (origin := ptr.toNat)
  have hhead : (multicallReturnMemory mem ptr.toNat bs).readWithPadding ptr.toNat 64 =
      (⟨32⟩ : UInt256).toByteArray ++ (UInt256.ofNat bs.length).toByteArray := by
    rw [multicallReturnMemory, hp.read ptr.toNat 64 (by have := h.lower; omega) (by omega)
      (by rw [multicallReturnStart_size]; omega), multicallReturnStart_read]
  rw [show 64 + 32 * bs.length + (bytesArrayTails bs).size =
      64 + (32 * bs.length + (bytesArrayTails bs).size) by omega,
    readWithPadding_split _ _ _ _ (by omega), hhead,
    readWithPadding_split _ _ _ _ (by exact hsize), hheads, htails]
  simp only [bytesArrayReturnBytes, ByteArray.append_assoc,
    show ptr.toNat + 64 + 32 * bs.length - ptr.toNat - 64 = 32 * bs.length by omega]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
