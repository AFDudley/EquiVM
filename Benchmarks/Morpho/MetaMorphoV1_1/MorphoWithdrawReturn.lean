import Benchmarks.Morpho.MetaMorphoV1_1.TwoWordReturnAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.CheckedArithmetic
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_084
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_085

/-! The withdrawal loop's caught-failure, decode-revert, and successful-subtraction branches. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem morphoWithdrawCaughtFailure {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr amount i assets : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨18881⟩
      (⟨0⟩ :: ptr :: amount :: i :: assets :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨18756⟩
      (amount :: amount :: i :: assets :: R) mem aw' out σ k' C' := by
  have h1 := metaMorphoV1_1_block_18881_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) rfl rd
  have h2 := metaMorphoV1_1_block_18887_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) rfl h1
  exact metaMorphoV1_1_block_18893_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2

set_option maxRecDepth 2000 in
theorem morphoWithdrawSuccessfulReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr amount i assets : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 13 ≤ 1024)
    (hout : out.size < UInt256.size) (hlong : 64 ≤ out.size)
    (hfit : allocationFits ptr ⟨64⟩) (hsub : amount.toNat ≤ assets.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨18881⟩
      (⟨1⟩ :: ptr :: amount :: i :: assets :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨18756⟩
      (⟨0⟩ :: ⟨0⟩ :: i :: UInt256.sub assets amount :: R)
      (writeWord mem 64 (nextCursor ptr ⟨64⟩)) aw' out σ k' C' := by
  have h1 := metaMorphoV1_1_block_18881_taken (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have h2 := metaMorphoV1_1_block_18916_fallthrough (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (ugt_zero (by simpa only [UInt256.toNat_ofNat_of_lt hout] using hlong)) h1
  have h3 := metaMorphoV1_1_block_18930 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
  obtain ⟨aw4, k4, C4, h4⟩ := twoWordReturnAllocationLong v
    (by simp only [List.length_cons]; omega) hfit
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h3
  have h5 := metaMorphoV1_1_block_18939 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h4
  have h6 := metaMorphoV1_1_block_18887_taken (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h5
  have h7 := metaMorphoV1_1_block_18899 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h6
  obtain ⟨k8, C8, h8⟩ := checkedSubReturn v (by simp only [List.length_cons]; omega) hsub
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h7
  have h9 := metaMorphoV1_1_block_18909 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h8
  exact metaMorphoV1_1_block_18893_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h9

set_option maxRecDepth 2000 in
theorem morphoWithdrawReturnReverts {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hout : out.size < UInt256.size) (hbad : ¬ (64 ≤ out.size ∧ allocationFits ptr ⟨64⟩))
    (rd : RD (deployedRuntime v) I g s0 ⟨18881⟩ (⟨1⟩ :: ptr :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_18881_taken (immWords := wordsOf (immStore v))
    (by omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hlong : 64 ≤ out.size
  · have h2 := metaMorphoV1_1_block_18916_fallthrough (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (ugt_zero (by simpa only [UInt256.toNat_ofNat_of_lt hout] using hlong)) h1
    have h3 := metaMorphoV1_1_block_18930 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    exact allocateRoundedRevert v (by simp only [List.length_cons]; omega)
      (fun hf ↦ hbad ⟨hlong, hf⟩) h3
  · have h2 := metaMorphoV1_1_block_18916_taken (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [ugt_one (by simpa only [UInt256.toNat_ofNat_of_lt hout] using
            Nat.lt_of_not_ge hlong)]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    exact twoWordReturnAllocationShort v (by simp only [List.length_cons]; omega) (by omega) h2

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
