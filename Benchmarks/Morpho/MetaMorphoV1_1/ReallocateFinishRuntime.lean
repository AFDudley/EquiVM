import Benchmarks.Morpho.MetaMorphoV1_1.Common
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_034

/-! The final reallocation conservation check and empty return. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem reallocateFinish {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {withdrawn supplied offset len saved : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨6789⟩
      ([withdrawn, offset, len, len, supplied, saved] ++ R) mem aw out σ k C) :
    (withdrawn ≠ supplied ∧ RDrev (deployedRuntime v) g s0) ∨
    (withdrawn = supplied ∧ RDret (deployedRuntime v) g s0 σ ByteArray.empty) := by
  by_cases he : withdrawn = supplied
  · have r1 := metaMorphoV1_1_block_6789_fallthrough (immWords := wordsOf (immStore v))
      (by dsimp only [List.append, List.length_cons]; omega)
      (by rw [he, u256_sub_self]; rfl) rd
    exact .inr ⟨he, metaMorphoV1_1_block_6796 (immWords := wordsOf (immStore v))
      (by dsimp only [metaMorphoV1_1_block_6789_fallthrough_stack, List.append, List.length_cons]; omega) r1⟩
  · have r1 := metaMorphoV1_1_block_6789_taken (immWords := wordsOf (immStore v))
      (by dsimp only [List.append, List.length_cons]; omega)
      (u256_sub_ne_zero_of_ne (Ne.symm he))
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact .inl ⟨he, metaMorphoV1_1_block_6797 (immWords := wordsOf (immStore v))
      (by dsimp only [metaMorphoV1_1_block_6789_taken_stack, List.append, List.length_cons]; omega) r1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
