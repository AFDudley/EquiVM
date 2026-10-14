import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawMorphoLoopState
import Benchmarks.Morpho.MetaMorphoV1_1.MinimumSource
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_084

/-! The minimum and nonzero test before a withdrawal attempt. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def withdrawMorphoMinimumFrame (frame : Frame) (liquidity assets : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "toWithdraw" (uint256Value (minimumWord liquidity assets)) }

theorem withdrawMorphoMinimumSource {frame : Frame} {evm : State} {liquidity assets : UInt256}
    (hcontract : frame.contract = contract)
    (hliquidity : frame.locals.get? "__c2" = some (uint256Value liquidity))
    (hassets : frame.locals.get? "assets" = some (uint256Value assets)) :
    ExecStmt config frame evm withdrawMorphoMinimum
      (.ok (withdrawMorphoMinimumFrame frame liquidity assets) evm) := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hcontract hliquidity hassets
  subst c
  apply minimumCall
  · simp only [evalExpr?, hliquidity, EvalResult.ofOption]
  · simp only [evalExpr?, hassets, EvalResult.ofOption]

set_option maxRecDepth 2000 in
theorem withdrawMorphoMinimumReach {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {liquidity params i assets : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨18738⟩
      ([liquidity, params, i, assets] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0
      (if minimumWord liquidity assets = ⟨0⟩ then ⟨18756⟩ else ⟨18776⟩)
      ([params, minimumWord liquidity assets, i, assets] ++ R) mem aw' rdata σ k' C' := by
  by_cases hz : minimumWord liquidity assets = ⟨0⟩
  · rw [if_pos hz]
    obtain ⟨aw', k', C', h⟩ := metaMorphoV1_1_block_18738_fallthrough_packed
      (immWords := wordsOf (immStore v)) hstack
      (by rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
        branchlessMinimum_sub_zero, minimumWord_comm assets liquidity]; exact hz) rd
    simp only [metaMorphoV1_1_block_18738_fallthrough_stack, branchlessMinimum_left, minimumWord_comm assets liquidity] at h
    exact ⟨aw', k', C', h⟩
  · rw [if_neg hz]
    obtain ⟨aw', k', C', h⟩ := metaMorphoV1_1_block_18738_taken_packed
      (immWords := wordsOf (immStore v)) hstack
      (by rw [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
        ne_eq, branchlessMinimum_sub_zero, minimumWord_comm assets liquidity]; exact hz)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [metaMorphoV1_1_block_18738_taken_stack, branchlessMinimum_left, minimumWord_comm assets liquidity] at h
    exact ⟨aw', k', C', h⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
