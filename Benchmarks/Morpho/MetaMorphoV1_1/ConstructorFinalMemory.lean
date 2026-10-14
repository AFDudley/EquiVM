import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStrictDecimalsInit
import Benchmarks.Morpho.MetaMorphoV1_1.WordCallBytePrefix

/-! Preserve the zero word and the initialized immutable region until the approval call. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

-- LIBRARY CANDIDATE: allocating a packed-word preimage preserves every earlier byte window.
theorem packedWordsMemory_bytePrefix (mem : ByteArray) (free : Nat) (words : List UInt256) :
    ByteMemoryPrefix mem (packedWordsMemory mem free words) free :=
  ((wordSequenceMemory_bytePrefix mem (free + 32) words).mono (by omega)).trans
    ((byteMemoryPrefix_writeWord _ free free _ (.inl (le_refl _))).trans
      (byteMemoryPrefix_writeWord _ 64 free _ (.inr (by decide))))

theorem constructorTimelockMemory_zeroPrefix (mem : ByteArray) (a : ConstructorArgs)
    (ok : Bool) (out : ByteArray) (I : ExecutionEnv)
    (hlo : 128 ≤ (constructorDecimalsCursor a out).toNat) :
    ByteMemoryPrefix mem (constructorTimelockMemory mem a ok out I) 128 := by
  have hasset : ByteMemoryPrefix mem (constructorAssetReadyMemory mem a ok out) 128 :=
    (byteMemoryPrefix_writeWord mem 160 128 _ (.inl (by decide))).trans
      ((byteMemoryPrefix_writeWord _ 128 128 _ (.inl (le_refl _))).trans
        (byteMemoryPrefix_writeWord _ 352 128 _ (.inl (by decide))))
  have hconstants : ByteMemoryPrefix (constructorAssetReadyMemory mem a ok out)
      (constructorDomainConstantsMemory (constructorAssetReadyMemory mem a ok out)) 128 :=
    (byteMemoryPrefix_writeWord _ 384 128 _ (.inl (by decide))).trans
      ((byteMemoryPrefix_writeWord _ 288 128 _ (.inl (by decide))).trans
        ((byteMemoryPrefix_writeWord _ 320 128 _ (.inl (by decide))).trans
          (byteMemoryPrefix_writeWord _ 224 128 _ (.inl (by decide)))))
  exact (hasset.trans hconstants).trans
    (((packedWordsMemory_bytePrefix _ (constructorDecimalsCursor a out).toNat
      (constructorDomainWords I)).mono hlo).trans
      ((byteMemoryPrefix_writeWord _ 192 128 _ (.inl (by decide))).trans
        ((byteMemoryPrefix_writeWord _ 256 128 _ (.inl (by decide))).trans
          (byteMemoryPrefix_writeWord _ ((constructorDecimalsCursor a out).toNat + 192)
            128 _ (.inl (by omega))))))

theorem constructorFinalDecimalsMemory_prefix (mem : ByteArray) (a : ConstructorArgs)
    (out strictOut : ByteArray) (hlo : 416 ≤ (constructorStrictDecimalsPtr a out).toNat)
    (hl : 32 ≤ strictOut.size) (hout : strictOut.size < UInt256.size) :
    ByteMemoryPrefix mem (constructorFinalDecimalsMemory mem a out strictOut) 416 :=
  (constructorMorphoMemory_prefix mem a.morpho _ hlo).trans
    ((constructorStrictDecimalsMemory_prefix
      (by simp only [constructorMorphoMemory, writeWord_sparse_size]; omega) hl hout).mono hlo)

theorem constructorFinalDecimalsMemory_morpho (mem : ByteArray) (a : ConstructorArgs)
    (out strictOut : ByteArray) (hlo : 448 ≤ (constructorStrictDecimalsPtr a out).toNat)
    (hl : 32 ≤ strictOut.size) (hout : strictOut.size < UInt256.size) :
    memLoad ⟨416⟩ (constructorFinalDecimalsMemory mem a out strictOut) = UInt256.ofNat a.morpho.val :=
  ((constructorStrictDecimalsMemory_prefix
    (by simp only [constructorMorphoMemory, writeWord_sparse_size]; omega) hl hout).load
      ⟨416⟩ (by decide) hlo
      (by simp only [constructorMorphoMemory, writeWord_sparse_size]; change 448 ≤ _; omega)).trans
    (constructorMorphoMemory_morpho mem a.morpho _ hlo)

end Benchmarks.Morpho.MetaMorphoV1_1
