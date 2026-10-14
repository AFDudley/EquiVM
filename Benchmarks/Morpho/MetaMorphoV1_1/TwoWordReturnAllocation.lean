import Benchmarks.Morpho.MetaMorphoV1_1.AllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_033
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_060
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_061
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009

/-! LIBRARY CANDIDATE: the shared allocator and decoder for two-word external returns. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem twoWordReturnAllocationLong {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hfit : allocationFits ptr ⟨64⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11329⟩
      (ptr :: ⟨64⟩ :: ⟨6415⟩ :: ⟨64⟩ :: ptr :: ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
      (memLoad (ptr + UInt256.ofNat 32) (writeWord mem 64 (nextCursor ptr ⟨64⟩)) ::
        memLoad ptr (writeWord mem 64 (nextCursor ptr ⟨64⟩)) :: R)
      (writeWord mem 64 (nextCursor ptr ⟨64⟩)) aw' out σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := allocateRoundedReturn v
    (by simp only [List.length_cons]; omega) hfit
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd
  have h2 := metaMorphoV1_1_block_6415 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  have h3 := metaMorphoV1_1_block_12090_fallthrough (immWords := wordsOf (immStore v))
    (by omega) (by rw [word_add_sub_left]; decide +kernel) h2
  exact metaMorphoV1_1_block_12103_packed (immWords := wordsOf (immStore v))
    (by omega) hret h3

set_option maxRecDepth 2000 in
theorem twoWordReturnAllocationShort {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hshort : out.size < 64)
    (rd : RD (deployedRuntime v) I g s0 ⟨6432⟩ (⟨64⟩ :: ptr :: ret :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_6432 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have h2 := metaMorphoV1_1_block_6405 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  by_cases hfit : allocationFits ptr (UInt256.ofNat out.size)
  · obtain ⟨aw3, k3, C3, h3⟩ := allocateRoundedReturn v
      (by simp only [List.length_cons]; omega) hfit
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2
    have h4 := metaMorphoV1_1_block_6415 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
    have h5 := metaMorphoV1_1_block_12090_taken (immWords := wordsOf (immStore v))
      (by omega)
      (by rw [word_add_sub_left, slt_ofNat_lit_one_low (by decide) hshort]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h4
    exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
      (by simp only [metaMorphoV1_1_block_12090_taken_stack, List.length_cons]; omega) h5
  · exact allocateRoundedRevert v (by simp only [List.length_cons]; omega) hfit h2

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
