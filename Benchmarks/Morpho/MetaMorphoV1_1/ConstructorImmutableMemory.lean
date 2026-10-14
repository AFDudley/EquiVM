import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorFinalImmutables

/-! Read the constructor's immutable words before and after the final external calls. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] constructorNameHash constructorVersionHash constructorDomainHash
set_option autoImplicit false

theorem constructorTimelockMemory_immutable (mem : ByteArray) (a : ConstructorArgs)
    (ok : Bool) (out : ByteArray) (I : ExecutionEnv) (strictOut : ByteArray)
    (hlo : 480 ≤ (constructorDecimalsCursor a out).toNat) {i : Nat} (hi : i < 9) :
    memLoad (UInt256.ofNat (128 + 32 * i)) (constructorTimelockMemory mem a ok out I) =
      (constructorImmutableValues a ok out I strictOut).getD i ⟨0⟩ := by
  have hsmall : 416 < UInt256.size := by decide
  have hs : 416 ≤ (constructorDomainConstantsMemory (constructorAssetReadyMemory mem a ok out)).size := by
    simp only [constructorDomainConstantsMemory, constructorNameHashMemory,
      constructorVersionImmutableMemory, writeWord_sparse_size]
    omega
  have hheap := packedWordsMemory_bytePrefix
    (constructorDomainConstantsMemory (constructorAssetReadyMemory mem a ok out))
    (constructorDecimalsCursor a out).toNat (constructorDomainWords I)
  have hp : 416 ≤ (constructorDomainAllocatedMemory (constructorAssetReadyMemory mem a ok out)
      I (constructorDecimalsCursor a out).toNat).size := le_trans hs hheap.size
  have hr (off : Nat) (h1 : 128 ≤ off) (h2 : off + 32 ≤ 416) :
      memLoad (UInt256.ofNat off)
          (constructorDomainAllocatedMemory (constructorAssetReadyMemory mem a ok out)
            I (constructorDecimalsCursor a out).toNat) =
        memLoad (UInt256.ofNat off) (constructorDomainConstantsMemory (constructorAssetReadyMemory mem a ok out)) :=
    hheap.load _ (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)
      (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)
      (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)
  have hself (m : ByteArray) (off : Nat) (word : UInt256) (hb : off < UInt256.size) :
      memLoad (UInt256.ofNat off) (writeWord m off word) = word :=
    memLoad_write_same _ _ _ _ (UInt256.toNat_ofNat_of_lt hb)
  interval_cases i <;>
    simp (disch := (first | omega | (simp (disch := decide) only
      [writeWord_sparse_size, UInt256.toNat_ofNat_of_lt]; omega))) only
      [Nat.reduceMul, Nat.reduceAdd, constructorTimelockMemory, constructorDomainReadyMemory,
        constructorDomainCachedMemory, memLoad_writeWord_disjoint, hr, hself,
        constructorImmutableValues, List.getD_cons_zero, List.getD_cons_succ]
  all_goals
    simp (disch := (first | omega | (simp (disch := decide) only
      [writeWord_sparse_size, UInt256.toNat_ofNat_of_lt]; omega))) only
      [constructorDomainConstantsMemory, constructorNameHashMemory, constructorVersionImmutableMemory,
        constructorAssetReadyMemory, constructorAssetMemory, memLoad_writeWord_disjoint, hself]

theorem constructorTimelockMemory_immutableSize (mem : ByteArray) (a : ConstructorArgs)
    (ok : Bool) (out : ByteArray) (I : ExecutionEnv) :
    416 ≤ (constructorTimelockMemory mem a ok out I).size := by
  have hs : 416 ≤ (constructorDomainConstantsMemory (constructorAssetReadyMemory mem a ok out)).size := by
    simp only [constructorDomainConstantsMemory, constructorNameHashMemory,
      constructorVersionImmutableMemory, writeWord_sparse_size]
    omega
  have hp := (packedWordsMemory_bytePrefix
    (constructorDomainConstantsMemory (constructorAssetReadyMemory mem a ok out))
    (constructorDecimalsCursor a out).toNat (constructorDomainWords I)).size
  simp only [constructorTimelockMemory, constructorDomainReadyMemory,
    constructorDomainCachedMemory, writeWord_sparse_size]
  change 416 ≤ max (max (max (packedWordsMemory _ _ _).size _) _) _
  omega

theorem constructorApprovalMemory_immutable {base mem final : ByteArray}
    (a : ConstructorArgs) (ok : Bool) (out strictOut : ByteArray) (I : ExecutionEnv)
    (hlo : 480 ≤ (constructorDecimalsCursor a out).toNat)
    (hptr : 480 ≤ (constructorStrictDecimalsPtr a out).toNat)
    (hl : 32 ≤ strictOut.size) (hout : strictOut.size < UInt256.size)
    (hpre : ByteMemoryPrefix (constructorTimelockMemory base a ok out I) mem 416)
    (hpost : ByteMemoryPrefix
      (writeWord (constructorFinalDecimalsMemory mem a out strictOut) 448
        (constructorDecimalsOffset (calldataWord strictOut 0))) final 480) :
    480 ≤ final.size ∧ ∀ i, i < 11 →
      memLoad (UInt256.ofNat (128 + 32 * i)) final =
        (constructorImmutableValues a ok out I strictOut).getD i ⟨0⟩ := by
  have hm0 := constructorTimelockMemory_immutableSize base a ok out I
  have hm : 416 ≤ mem.size := le_trans hm0 hpre.size
  have hp := constructorFinalDecimalsMemory_prefix mem a out strictOut (by omega) hl hout
  have hm1 : 448 ≤ (constructorFinalDecimalsMemory mem a out strictOut).size := by
    have hs := (constructorStrictDecimalsMemory_prefix
      (mem := constructorMorphoMemory mem a.morpho (constructorStrictDecimalsPtr a out))
      (ptr := constructorStrictDecimalsPtr a out) (out := strictOut)
      (by simp only [constructorMorphoMemory, writeWord_sparse_size]; omega) hl hout).size
    exact le_trans (by simp only [constructorMorphoMemory, writeWord_sparse_size]; omega) hs
  have hm2 : 480 ≤ (writeWord (constructorFinalDecimalsMemory mem a out strictOut) 448
      (constructorDecimalsOffset (calldataWord strictOut 0))).size := by
    rw [writeWord_sparse_size]; omega
  refine ⟨le_trans hm2 hpost.size, ?_⟩
  intro i hi
  have hn : (UInt256.ofNat (128 + 32 * i)).toNat = 128 + 32 * i :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2 ^ 256; omega)
  rw [hpost.load _ (by rw [hn]; omega) (by rw [hn]; omega) (by rw [hn]; omega)]
  by_cases hi9 : i < 9
  · rw [memLoad_writeWord_disjoint _ 448 _ _ (by rw [hn]; omega) (.inl (by rw [hn]; omega)),
      hp.load _ (by rw [hn]; omega) (by rw [hn]; omega) (by rw [hn]; omega),
      hpre.load _ (by rw [hn]; omega) (by rw [hn]; omega) (by rw [hn]; omega)]
    exact constructorTimelockMemory_immutable base a ok out I strictOut hlo hi9
  · have hi' : i = 9 ∨ i = 10 := by omega
    rcases hi' with rfl | rfl
    · rw [memLoad_writeWord_disjoint _ 448 _ _ (by change 448 ≤ _; exact hm1) (.inl (by decide))]
      exact constructorFinalDecimalsMemory_morpho mem a out strictOut (by omega) hl hout
    · exact memLoad_write_same _ _ _ _ rfl

end Benchmarks.Morpho.MetaMorphoV1_1
