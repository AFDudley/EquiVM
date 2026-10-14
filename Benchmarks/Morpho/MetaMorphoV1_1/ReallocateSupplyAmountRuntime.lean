import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateSupplyAmountSource
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_033
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_034

/-! Runtime supply-amount selection and the zero-amount continue path. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem reallocateSupplyAmountRuntime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {target assets shares allocation assetsPtr amount withdrawn id offset i len supplied saved : UInt256}
    {R : List UInt256} (v : MetaMorphoV1_1Immutables) (hstack : R.length + 13 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨6450⟩
      ([target, assets, shares, allocation, assetsPtr, amount, withdrawn, id, offset, i, len, supplied, saved] ++ R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨6479⟩
      ([assets, allocation, supplied, reallocateSupplyAmount target assets supplied withdrawn,
        id, offset, withdrawn, len, i, saved] ++ R) mem aw' rdata σ k' C' := by
  by_cases ht : target = UInt256.lnot ⟨0⟩
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_6450_fallthrough_packed
      (immWords := wordsOf (immStore v)) (by dsimp only [List.append, List.length_cons]; omega)
      (by rw [ht, u256_eq_refl]; decide) rd
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_6470_packed
      (immWords := wordsOf (immStore v)) (by dsimp only [List.append, List.length_cons]; omega) h1
    exact ⟨aw2, k2, C2, by simpa only [metaMorphoV1_1_block_6470_stack, wordZeroFloorSub,
      reallocateSupplyAmount, if_pos ht] using h2⟩
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_6450_taken_packed
      (immWords := wordsOf (immStore v)) (by dsimp only [List.append, List.length_cons]; omega)
      (by rw [u256_eq_of_ne ht]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_6757_packed
      (immWords := wordsOf (immStore v)) (by dsimp only [List.append, List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    exact ⟨aw2, k2, C2, by simpa only [metaMorphoV1_1_block_6757_stack, wordZeroFloorSub,
      reallocateSupplyAmount, if_neg ht] using h2⟩

set_option maxRecDepth 2000 in
theorem reallocateSupplyContinueRuntime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {assets allocation supplied amount id offset withdrawn len i saved : UInt256}
    {R : List UInt256} (v : MetaMorphoV1_1Immutables) (hstack : R.length + 12 ≤ 1024)
    (hz : amount = ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨6479⟩
      ([assets, allocation, supplied, amount, id, offset, withdrawn, len, i, saved] ++ R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨6380⟩
      ([i, ⟨1⟩, offset, withdrawn, len, supplied, saved] ++ R) mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_6479_taken_packed
    (immWords := wordsOf (immStore v)) (by dsimp only [List.append, List.length_cons]; omega)
    (by rw [hz]; decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_6743_packed (immWords := wordsOf (immStore v))
    (by dsimp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
