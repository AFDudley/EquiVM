import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoArithmeticSource
import Benchmarks.Morpho.MetaMorphoV1_1.SharesToAssetsUpRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_081

/-! Refine the supply amount calculation and the compiler's branchless nonzero test. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem supplyMorphoArithmeticSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem market : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {shares marketPtr cap params i morpho assets : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 15 ≤ 1024)
    (hcontract : frame.contract = contract)
    (hshares : frame.locals.get? "supplyShares" = some (uint256Value shares))
    (hmarket : frame.locals.get? "market" = some (marketValue market))
    (hcap : frame.locals.get? "supplyCap" = some (uint256Value cap))
    (hassets : frame.locals.get? "assets" = some (uint256Value assets))
    (hc : MarketChecks market)
    (hsa : memLoad marketPtr mem = calldataWord market 0)
    (hss : memLoad (marketPtr + ⟨32⟩) mem = calldataWord market 32)
    (rd : RD (deployedRuntime v) I g s0 ⟨18119⟩
      ([shares, marketPtr, ⟨18144⟩, cap, params, i, morpho, assets] ++ R)
      mem aw rdata σ k C) :
    (ExecBlock config frame evm supplyMorphoArithmetic .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (ExecBlock config frame evm supplyMorphoArithmetic
        (.ok (supplyMorphoArithmeticFrame frame shares (calldataWord market 0)
          (calldataWord market 32) cap assets) evm) ∧
      let amount := supplyMorphoAmount shares (calldataWord market 0) (calldataWord market 32) cap assets
      ∃ aw' k' C', RD (deployedRuntime v) I g s0
        (if amount = ⟨0⟩ then ⟨18168⟩ else ⟨18186⟩)
        ([params, amount, i, morpho, assets] ++ R) mem aw' rdata σ k' C') := by
  have hmask (w : UInt256) (hw : w.toNat < 2 ^ 128) :
      UInt256.land w (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
        (UInt256.ofNat 1)) = w :=
    u256LandMaskCleanOfToNat _ _ (by decide +kernel) hw
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_18119_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have hss' : memLoad (marketPtr + UInt256.ofNat 32) mem = calldataWord market 32 := hss
  simp only [metaMorphoV1_1_block_18119_stack, hsa, hss',
    hmask _ hc.2.1, hmask _ hc.2.2.1] at h1
  by_cases hfit : assetsUpFits shares (calldataWord market 0) (calldataWord market 32)
  · obtain ⟨k2, C2, h2⟩ := assetsUpReturn v
      (by simp only [List.append, List.length_cons]; omega) hfit
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
    refine .inr ⟨supplyMorphoArithmeticSource hcontract hshares hmarket hcap hassets hfit, ?_⟩
    dsimp only
    by_cases hz : supplyMorphoAmount shares (calldataWord market 0) (calldataWord market 32)
        cap assets = ⟨0⟩
    · rw [if_pos hz]
      obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_18144_fallthrough_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
        (by rw [wordZeroFloorSub, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
          branchlessMinimum_sub_zero]; exact hz) h2
      simp only [metaMorphoV1_1_block_18144_fallthrough_stack, wordZeroFloorSub,
        branchlessMinimum_left] at h3
      exact ⟨aw3, k3, C3, h3⟩
    · rw [if_neg hz]
      obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_18144_taken_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
        (by rw [wordZeroFloorSub, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
          ne_eq, branchlessMinimum_sub_zero]; exact hz)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
      simp only [metaMorphoV1_1_block_18144_taken_stack, wordZeroFloorSub,
        branchlessMinimum_left] at h3
      exact ⟨aw3, k3, C3, h3⟩
  · exact .inl ⟨ExecBlock.consRevert
      (supplyMorphoConversionReverts hcontract hshares hmarket hfit),
      assetsUpRevert v (by simp only [List.append, List.length_cons]; omega) hfit h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
