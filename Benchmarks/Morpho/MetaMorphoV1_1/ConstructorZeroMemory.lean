import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStorageMemory

/-! The zero-length sentinel at memory offset 96 survives constructor allocations. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

-- LIBRARY CANDIDATE: byte-prefix preservation also preserves in-bounds MLOADs.
theorem SourceMemory.ByteMemoryPrefix.load {before after : ByteArray} {limit : Nat}
    (h : ByteMemoryPrefix before after limit) (ptr : UInt256)
    (hlo : 96 ≤ ptr.toNat) (hhi : ptr.toNat + 32 ≤ limit)
    (hin : ptr.toNat + 32 ≤ before.size) : memLoad ptr after = memLoad ptr before := by
  have hs := h.size
  simp only [memLoad, if_neg (show ¬ ptr.toNat ≥ after.size by omega),
    if_neg (show ¬ ptr.toNat ≥ before.size by omega), h.read _ _ hlo hhi hin]

theorem constructorArgumentMemory_zero (a : ConstructorArgs) :
    memLoad ⟨96⟩ (constructorArgumentMemory a) = ⟨0⟩ := by
  apply loadedWord_of_read
  · change 96 + 32 ≤ _
    rw [constructorArgumentMemory_size]; omega
  · change (constructorArgumentMemory a).readWithPadding 96 32 = _
    rw [readWithPadding_eq_extract _ _ (by rw [constructorArgumentMemory_size]; omega),
      constructorArgumentMemory, extract_append_left _ _ _ _ (by
        rw [ByteArray.size_append, constructorAllocatedMemory_size, ByteArray_zeroes_size]; omega),
      extract_append_right_window _ _ _ _ (by rw [constructorAllocatedMemory_size]),
      constructorAllocatedMemory_size]
    decide +kernel

theorem constructorVersionMemory_zero (a : ConstructorArgs)
    (hbound : 23666 + a.encoded.length < UInt256.size) (hsmall : a.argumentEnd < 2 ^ 64) :
    128 ≤ (constructorVersionMemory (constructorStringsMemory a) a.stringsEnd).size ∧
    memLoad ⟨96⟩ (constructorVersionMemory (constructorStringsMemory a) a.stringsEnd) = ⟨0⟩ := by
  have ha : 128 ≤ a.argumentEnd := by unfold ConstructorArgs.argumentEnd; omega
  have hn : 128 ≤ a.nameEnd := by unfold ConstructorArgs.nameEnd; omega
  have hs : 128 ≤ a.stringsEnd := by unfold ConstructorArgs.stringsEnd; omega
  have hp := ((constructorNameMemory_prefix a hsmall).mono ha).trans
    (((constructorStringsMemory_prefix a hbound hsmall).mono hn).trans
      ((constructorVersionMemory_prefix (constructorStringsMemory a) a.stringsEnd).mono hs))
  have hm : 128 ≤ (constructorArgumentMemory a).size := by
    rw [constructorArgumentMemory_size]; omega
  exact ⟨le_trans hm hp.size,
    (hp.load ⟨96⟩ (by decide) (by decide) hm).trans (constructorArgumentMemory_zero a)⟩

end Benchmarks.Morpho.MetaMorphoV1_1
