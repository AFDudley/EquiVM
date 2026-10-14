import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateEventRuntime

/-! The withdrawal event and checked total return to the reallocation loop increment. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem reallocateWithdrawFinishRuntime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr shares assets withdrawn id offset i len supplied saved : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 14 ≤ 1024)
    (hperm : I.perm = true) (hfree : memLoad ⟨64⟩ mem = ptr) (hptr : ptr.toNat < 2 ^ 64)
    (rd : RD (deployedRuntime v) I g s0 ⟨6423⟩
      ([shares, assets, withdrawn, id, ⟨6378⟩, ⟨1⟩, offset, i, len, supplied, saved] ++ R)
      mem aw rdata σ k C) :
    (UInt256.size ≤ withdrawn.toNat + assets.toNat ∧ RDrev (deployedRuntime v) g s0) ∨
    (withdrawn.toNat + assets.toNat < UInt256.size ∧ ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨6380⟩
      ([i, ⟨1⟩, offset, withdrawn + assets, len, supplied, saved] ++ R)
      (reallocateEventMemory mem ptr assets shares) aw' rdata σ k' C') := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_6423_packed
    (immWords := wordsOf (immStore v)) (by dsimp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨aw2, k2, C2, h2⟩ := reallocateEventRuntime v false
    (by dsimp only [List.append, List.length_cons]; omega) hperm hfree hptr h1
  by_cases hfit : withdrawn.toNat + assets.toNat < UInt256.size
  · obtain ⟨k3, C3, h3⟩ := checkedAddReturn v
      (by dsimp only [List.append, List.length_cons]; omega) hfit
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2
    obtain ⟨aw4, k4, C4, h4⟩ := metaMorphoV1_1_block_6378_packed
      (immWords := wordsOf (immStore v)) (by dsimp only [List.append, List.length_cons]; omega) h3
    exact .inr ⟨hfit, aw4, k4, C4, h4⟩
  · exact .inl ⟨Nat.le_of_not_gt hfit, checkedAddRevert v
      (by dsimp only [List.append, List.length_cons]; omega) (Nat.le_of_not_gt hfit) h2⟩

set_option maxRecDepth 2000 in
theorem reallocateWithdrawFinishRuntimeStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {shares assets withdrawn id offset i len supplied saved : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 14 ≤ 1024) (hperm : I.perm = false)
    (rd : RD (deployedRuntime v) I g s0 ⟨6423⟩
      ([shares, assets, withdrawn, id, ⟨6378⟩, ⟨1⟩, offset, i, len, supplied, saved] ++ R)
      mem aw rdata σ k C) : RDstatic (deployedRuntime v) g s0 := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_6423_packed
    (immWords := wordsOf (immStore v)) (by dsimp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact reallocateWithdrawEventStatic (immWords := wordsOf (immStore v))
    (by dsimp only [List.append, List.length_cons]; omega) hperm h1

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
