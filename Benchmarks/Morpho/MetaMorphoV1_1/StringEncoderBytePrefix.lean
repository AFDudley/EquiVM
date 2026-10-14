import Benchmarks.Morpho.MetaMorphoV1_1.ByteMemoryPrefix
import Benchmarks.Morpho.MetaMorphoV1_1.StringEncoderMemory

/-! The dynamic bytes encoder preserves every earlier allocated byte window. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

-- GENERALIZES stringPayloadMemory_prefix to payloads with an unpadded final word.
theorem stringPayloadMemory_bytePrefix (mem : ByteArray) (src dest : Nat) (len : UInt256)
    (hin : src + len.toNat ≤ mem.size) :
    ByteMemoryPrefix mem (stringPayloadMemory mem src dest len) dest := by
  exact (byteMemoryPrefix_writeWord mem dest dest len (.inl (le_refl _))).trans
    ((byteMemoryPrefix_copy _ _ src (dest + 32) len.toNat dest
      (by rw [writeWord_sparse_size]; omega)
      (by rw [writeWord_sparse_size]; omega) (by omega)).trans
      (byteMemoryPrefix_writeWord _ (dest + 32 + len.toNat) dest ⟨0⟩ (.inl (by omega))))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
