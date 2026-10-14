import Benchmarks.Morpho.MetaMorphoV1_1.EncodedWordCallMemory
import Benchmarks.Morpho.MetaMorphoV1_1.ByteMemoryPrefix

/-! Fixed-word call construction preserves all earlier allocated byte buffers. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

-- LIBRARY CANDIDATE: byte-window counterpart of wordSequenceMemory_prefix.
theorem wordSequenceMemory_bytePrefix (mem : ByteArray) (off : Nat) (words : List UInt256) :
    ByteMemoryPrefix mem (wordSequenceMemory mem off words) off := by
  induction words generalizing mem off with
  | nil => exact .refl _ _
  | cons word words ih =>
      exact (byteMemoryPrefix_writeWord mem off off word (.inl (le_refl _))).trans
        ((ih _ (off + 32)).mono (by omega))

-- LIBRARY CANDIDATE: preservation of arbitrary byte windows below an ABI word request.
theorem allocatedWordCallMemory_bytePrefix (mem : ByteArray) (ptr selector : UInt256)
    (words : List UInt256) :
    ByteMemoryPrefix mem (allocatedWordCallMemory mem ptr selector words) ptr.toNat := by
  exact (byteMemoryPrefix_writeWord mem (ptr.toNat + 32) ptr.toNat selector (.inl (by omega))).trans
    (((wordSequenceMemory_bytePrefix _ (ptr.toNat + 32 + 4) words).mono (by omega)).trans
      ((byteMemoryPrefix_writeWord _ ptr.toNat ptr.toNat _ (.inl (le_refl _))).trans
        (byteMemoryPrefix_writeWord _ 64 ptr.toNat _ (.inr (by decide)))))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
