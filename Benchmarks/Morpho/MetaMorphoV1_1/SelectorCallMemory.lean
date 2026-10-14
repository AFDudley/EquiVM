import Benchmarks.Morpho.MetaMorphoV1_1.EncodedWordCallMemory
import Benchmarks.Morpho.MetaMorphoV1_1.BytesBuffer

/-! The zero-argument case of a length-prefixed, allocated ABI request. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

-- LIBRARY CANDIDATE: selector-only requests share the static-word request representation.
theorem allocatedSelectorCall_buffer (mem : ByteArray) (ptr selector : UInt256)
    (hlo : 96 ≤ ptr.toNat) :
    BytesBuffer (allocatedWordCallMemory mem ptr selector []) ptr
      (selector.toByteArray.extract 0 4) := by
  have hs : (selector.toByteArray.extract 0 4).size = 4 := by
    rw [ByteArray.size_extract, toByteArray_size]; decide
  have hb : BytesBuffer (encodedWordCallMemory mem ptr selector []) ptr
      (selector.toByteArray.extract 0 4) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hs]
      change ptr.toNat + 32 + 4 ≤
        (writeWord (writeWord mem (ptr.toNat + 32) selector) ptr.toNat ⟨4⟩).size
      simp only [writeWord_sparse_size]; omega
    · rw [hs]
      exact memLoad_write_same _ _ _ _ rfl
    · rw [hs]
      change (writeWord (writeWord mem (ptr.toNat + 32) selector) ptr.toNat ⟨4⟩).readWithPadding
        (ptr.toNat + 32) 4 = _
      rw [writeWord_sparse_read_preserved_unbounded _ _ _ _ _
        (by rw [writeWord_sparse_size]; omega) (.inr (by omega))]
      have hr := writeWord_sparse_read_window mem (ptr.toNat + 32) 0 4 selector
        (by decide) (by decide) (by decide)
      simpa only [Nat.add_zero] using hr
  exact hb.writeWord 64 _ (.inr hlo)

theorem allocatedSelectorCall_bytePrefix (mem : ByteArray) (ptr selector : UInt256) :
    ByteMemoryPrefix mem (allocatedWordCallMemory mem ptr selector []) ptr.toNat :=
  (byteMemoryPrefix_writeWord mem (ptr.toNat + 32) ptr.toNat selector (.inl (by omega))).trans
    ((byteMemoryPrefix_writeWord _ ptr.toNat ptr.toNat ⟨4⟩ (.inl (le_refl _))).trans
      (byteMemoryPrefix_writeWord _ 64 ptr.toNat _ (.inr (by decide))))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
