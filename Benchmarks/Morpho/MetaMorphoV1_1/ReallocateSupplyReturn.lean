import Benchmarks.Morpho.MetaMorphoV1_1.TwoWordReturnAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_034
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_018

/-! Strict failure propagation and two-word return decoding for reallocation supplies. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem reallocateSupplyCallFailure {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr id amount x : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hout : out.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨6610⟩ (⟨0⟩ :: id :: amount :: ptr :: x :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_6610_taken (immWords := wordsOf (immStore v))
    (by omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_2921 (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1_block_6610_taken_stack, List.length_cons]; omega)
    (by change 0 + (UInt256.ofNat out.size).toNat ≤ out.size
        rw [UInt256.toNat_ofNat_of_lt hout, Nat.zero_add]) h1

set_option maxRecDepth 2000 in
theorem reallocateSupplyReturnAllocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr id amount x : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 14 ≤ 1024)
    (hout : out.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨6610⟩ (⟨1⟩ :: id :: amount :: ptr :: x :: R)
      mem aw out σ k C) :
    (¬ (64 ≤ out.size ∧ allocationFits ptr ⟨64⟩) ∧ RDrev (deployedRuntime v) g s0) ∨
    (64 ≤ out.size ∧ allocationFits ptr ⟨64⟩ ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨6716⟩
        (memLoad (ptr + UInt256.ofNat 32) (writeWord mem 64 (nextCursor ptr ⟨64⟩)) ::
          memLoad ptr (writeWord mem 64 (nextCursor ptr ⟨64⟩)) :: x :: id :: amount :: ⟨6686⟩ :: ⟨1⟩ :: R)
        (writeWord mem 64 (nextCursor ptr ⟨64⟩)) aw' out σ k' C') := by
  have h1 := metaMorphoV1_1_block_6610_fallthrough (immWords := wordsOf (immStore v))
    (by omega) (by decide) rd
  have h2 := metaMorphoV1_1_block_6617_taken (immWords := wordsOf (immStore v))
    (by omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  by_cases hl : 64 ≤ out.size
  · have h3 := metaMorphoV1_1_block_6692_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (ugt_zero (by simpa only [UInt256.toNat_ofNat_of_lt hout] using hl)) h2
    have h4 := metaMorphoV1_1_block_6707 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
    by_cases hf : allocationFits ptr ⟨64⟩
    · obtain ⟨aw5, k5, C5, h5⟩ := twoWordReturnAllocationLong v
        (by simp only [List.length_cons]; omega) hf
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h4
      exact .inr ⟨hl, hf, aw5, k5, C5, h5⟩
    · exact .inl ⟨fun hgood ↦ hf hgood.2,
        allocateRoundedRevert v (by simp only [List.length_cons]; omega) hf h4⟩
  · have h3 := metaMorphoV1_1_block_6692_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [ugt_one (by simpa only [UInt256.toNat_ofNat_of_lt hout] using
            Nat.lt_of_not_ge hl)]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    exact .inl ⟨fun hgood ↦ hl hgood.1,
      twoWordReturnAllocationShort v (by simp only [List.length_cons]; omega) (by omega) h3⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
