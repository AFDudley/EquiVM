import Benchmarks.Morpho.MetaMorphoV1_1.MulticallInitialMemory
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_022
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_023

/-! Initialize every pointer in the multicall result array. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem multicallInitLoop {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C i n : Nat}
    {base : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (remaining : Nat) (hstack : R.length + 10 ≤ 1024)
    (hfit : 160 + 32 * n < UInt256.size) (hdiff : n = i + remaining)
    (rd : RD (deployedRuntime v) I g s0 ⟨3856⟩
      (UInt256.ofNat (32 * i) :: UInt256.ofNat (32 * n) :: UInt256.ofNat n :: base :: ⟨128⟩ :: R)
      mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨3864⟩
      (UInt256.ofNat (32 * n) :: UInt256.ofNat (32 * n) :: UInt256.ofNat n :: base :: ⟨128⟩ :: R)
      (wordSequenceMemory mem (160 + 32 * i) (wordArrayWords (fun _ ↦ ⟨96⟩) i remaining))
      aw' out σ k' C' := by
  induction remaining generalizing mem aw k C i with
  | zero =>
      have he : i = n := by omega
      subst i
      have r1 := metaMorphoV1_1_block_3856_fallthrough (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) (ult_zero (le_refl _)) rd
      exact ⟨_, _, _, r1⟩
  | succ rem ih =>
      have hi : i < n := by omega
      have r1 := metaMorphoV1_1_block_3856_taken (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [ult_one (by rw [UInt256.toNat_ofNat_of_lt (show 32 * i < UInt256.size by omega),
              UInt256.toNat_ofNat_of_lt (show 32 * n < UInt256.size by omega)]; omega)]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      obtain ⟨aw2, k2, C2, r2⟩ := metaMorphoV1_1_block_4106_packed
        (immWords := wordsOf (immStore v)) (by omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
      have ha : UInt256.ofNat (32 * i) + UInt256.ofNat 32 = UInt256.ofNat (32 * (i + 1)) := by
        rw [ofNat_add_words]; congr 1
      have hs : (((⟨128⟩ : UInt256) + UInt256.ofNat (32 * i)) + UInt256.ofNat 32).toNat =
          160 + 32 * i := by
        change ((UInt256.ofNat 128 + UInt256.ofNat (32 * i)) + UInt256.ofNat 32).toNat = _
        rw [ofNat_add_words, ofNat_add_words,
          UInt256.toNat_ofNat_of_lt (show 128 + 32 * i + 32 < UInt256.size by omega)]
        omega
      simp only [metaMorphoV1_1_block_4106_stack, metaMorphoV1_1_block_4106_memory, ha, hs] at r2
      obtain ⟨aw3, k3, C3, r3⟩ := ih (by omega) r2
      refine ⟨aw3, k3, C3, ?_⟩
      simpa only [wordArrayWords, wordSequenceMemory,
        show 160 + 32 * i + 32 = 160 + 32 * (i + 1) by omega] using r3

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
