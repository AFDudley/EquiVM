import Benchmarks.Morpho.MetaMorphoV1_1.AccruedAssetsQueueRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawMorphoLoopState
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_084

/-! Read the next withdrawal market from the queue. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem withdrawMorphoQueueRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {i assets : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (hbound : i.toNat < (codeOwnerStorageWord I σ ⟨21⟩).toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨18674⟩
      ([i, assets] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨16116⟩
      ([accruedAssetsIdWord I σ i, ⟨18704⟩, ⟨18711⟩, ⟨18738⟩,
        accruedAssetsIdWord I σ i, i, assets] ++ R)
      (wordAt0Mem ⟨21⟩ mem) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_18674_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨k2, C2, h2⟩ := withdrawQueueIndex v
    (by simp only [List.append, List.length_cons]; omega) hbound
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_18682_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
  have hshift : UInt256.shiftRight
      (codeOwnerStorageWord I σ (accruedAssetsQueueSlot i))
        (UInt256.shiftLeft ⟨0⟩ (UInt256.ofNat 3)) =
      accruedAssetsIdWord I σ i := wordShiftRight_zero _
  dsimp only [codeOwnerStorageWord, accruedAssetsQueueSlot] at hshift
  exact ⟨aw3, k3, C3, by simpa only [metaMorphoV1_1_block_18682_stack, hshift] using h3⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
