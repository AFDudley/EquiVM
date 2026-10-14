import Benchmarks.Morpho.MetaMorphoV1_1.TwoWordReturnAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_032
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_018

/-! Strict failure propagation and two-word return decoding for reallocation withdrawals. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem reallocateWithdrawCallFailure {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr x : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hout : out.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨6300⟩ (⟨0⟩ :: ptr :: x :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_6300_taken (immWords := wordsOf (immStore v))
    (by omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_2921 (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1_block_6300_taken_stack, List.length_cons]; omega)
    (by change 0 + (UInt256.ofNat out.size).toNat ≤ out.size
        rw [UInt256.toNat_ofNat_of_lt hout, Nat.zero_add]) h1

set_option maxRecDepth 2000 in
theorem reallocateWithdrawReturnAllocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr x y : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 13 ≤ 1024)
    (hout : out.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨6300⟩ (⟨1⟩ :: ptr :: x :: y :: R)
      mem aw out σ k C) :
    (¬ (64 ≤ out.size ∧ allocationFits ptr ⟨64⟩) ∧ RDrev (deployedRuntime v) g s0) ∨
    (64 ≤ out.size ∧ allocationFits ptr ⟨64⟩ ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨6423⟩
        (memLoad (ptr + UInt256.ofNat 32) (writeWord mem 64 (nextCursor ptr ⟨64⟩)) ::
          memLoad ptr (writeWord mem 64 (nextCursor ptr ⟨64⟩)) :: x :: y :: ⟨6378⟩ :: ⟨1⟩ :: R)
        (writeWord mem 64 (nextCursor ptr ⟨64⟩)) aw' out σ k' C') := by
  have h1 := metaMorphoV1_1_block_6300_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by decide) rd
  have h2 := metaMorphoV1_1_block_6307_taken (immWords := wordsOf (immStore v))
    (by omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  by_cases hl : 64 ≤ out.size
  · have h3 := metaMorphoV1_1_block_6387_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (ugt_zero (by simpa only [UInt256.toNat_ofNat_of_lt hout] using hl)) h2
    have h4 := metaMorphoV1_1_block_6405 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
    by_cases hf : allocationFits ptr ⟨64⟩
    · obtain ⟨aw5, k5, C5, h5⟩ := twoWordReturnAllocationLong v
        (by simp only [List.length_cons]; omega) hf
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h4
      exact .inr ⟨hl, hf, aw5, k5, C5, h5⟩
    · exact .inl ⟨fun hgood ↦ hf hgood.2,
        allocateRoundedRevert v (by simp only [List.length_cons]; omega) hf h4⟩
  · have h3 := metaMorphoV1_1_block_6387_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [ugt_one (by simpa only [UInt256.toNat_ofNat_of_lt hout] using
            Nat.lt_of_not_ge hl)]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    exact .inl ⟨fun hgood ↦ hl hgood.1,
      twoWordReturnAllocationShort v (by simp only [List.length_cons]; omega) (by omega) h3⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
