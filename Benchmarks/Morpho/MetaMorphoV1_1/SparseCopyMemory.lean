import Benchmarks.Morpho.MetaMorphoV1_1.ByteMemoryPrefix

/-! Byte-copy facts that also cover a destination beyond the currently written memory. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

-- LIBRARY CANDIDATE: copyWindow_size without a destination-in-memory hypothesis.
theorem copyWindow_sparse_size (src mem : ByteArray) (srcOff dest len : Nat)
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) :
    (src.write srcOff mem dest len).size = max mem.size (dest + len) := by
  by_cases hd : dest ≤ mem.size
  · exact copyWindow_size src mem srcOff dest len hpos hsrc hd
  · rw [byteArray_write_from_ge_eq_no_gap_bound src mem srcOff dest len hpos hsrc (by omega)]
    simp only [ByteArray.size_append, ByteArray_zeroes_size, ByteArray.size_extract]
    omega

-- LIBRARY CANDIDATE: the exact copied window, including a zero-filled gap before it.
theorem copyWindow_sparse_extract (src mem : ByteArray) (srcOff dest len : Nat)
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) :
    (src.write srcOff mem dest len).extract dest (dest + len) = src.extract srcOff (srcOff + len) := by
  by_cases hd : dest ≤ mem.size
  · simpa only [Nat.add_zero] using copyWindow_extract src mem srcOff dest len 0 len hpos hsrc hd
      (by omega)
  · have hs : (mem ++ ByteArray.zeroes (dest - mem.size)).size = dest := by
      rw [ByteArray.size_append, ByteArray_zeroes_size]; omega
    rw [byteArray_write_from_ge_eq_no_gap_bound src mem srcOff dest len hpos hsrc (by omega)]
    exact extract_append_right' _ _ _ _ hs.symm (by rw [hs, ByteArray.size_extract]; omega)

-- LIBRARY CANDIDATE: byte-window preservation below a sparse copy destination.
theorem byteMemoryPrefix_copy_sparse (src mem : ByteArray) (srcOff dest len : Nat)
    (hsrc : srcOff + len ≤ src.size) :
    ByteMemoryPrefix mem (src.write srcOff mem dest len) dest := by
  by_cases hz : len = 0
  · rw [hz, byteArray_write_len_zero]; exact .refl _ _
  by_cases hd : dest ≤ mem.size
  · exact byteMemoryPrefix_copy src mem srcOff dest len dest hsrc hd (le_refl _)
  have hs : mem.size ≤ (src.write srcOff mem dest len).size := by
    rw [copyWindow_sparse_size src mem srcOff dest len hz hsrc]; omega
  refine ⟨hs, fun off count _ _ hin ↦ ?_⟩
  by_cases hc : count = 0
  · simp only [hc, byteArray_readWithPadding_zero]
  rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega) (le_trans hin hs),
    readWithPadding_eq_extract_unbounded _ _ _ (by omega) hin,
    byteArray_write_from_ge_eq_no_gap_bound src mem srcOff dest len hz hsrc (by omega),
    extract_append_left _ _ _ _ (by rw [ByteArray.size_append]; omega),
    extract_append_left _ _ _ _ hin]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
