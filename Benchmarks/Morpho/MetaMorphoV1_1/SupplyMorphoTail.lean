import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoLoopState
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_081
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_062

/-! Early return or the loop's increment after a supply attempt. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem supplyMorphoTailSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {scratch0 scratch1 ptr i assets morpho savedMorpho ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (ha : frame.locals.get? "assets" = some (uint256Value assets))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨18168⟩
      ([scratch0, scratch1, i, morpho, assets, savedMorpho, ret] ++ R) mem aw rdata σ k C) :
    (assets = ⟨0⟩ ∧ ExecStmt config frame evm supplyMorphoSupply[1]!
        (.returned frame evm (some [.tuple [], uint256Value ptr])) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R mem aw' rdata σ k' C') ∨
    (assets ≠ ⟨0⟩ ∧ ExecStmt config frame evm supplyMorphoSupply[1]! (.ok frame evm) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨18180⟩
        ([i, ⟨1⟩, morpho, assets, savedMorpho, ret] ++ R) mem aw' rdata σ k' C') := by
  have htest := supplyMorphoDoneCondition (evm := evm) ha
  by_cases hz : assets = ⟨0⟩
  · rw [decide_eq_true hz] at htest
    obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_18168_taken_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
      (by rw [hz]; decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_12579_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append]; omega) hret h1
    exact .inl ⟨hz, ExecStmt.iteTrue htest (ExecBlock.consReturn (supplyMorphoReturnSource hp)),
      aw2, k2, C2, h2⟩
  · rw [decide_eq_false hz] at htest
    obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_18168_fallthrough_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
      (isZero_eq_zero_of_ne hz) rd
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_18177_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega) h1
    exact .inr ⟨hz, ExecStmt.iteFalse htest ExecBlock.nil, aw2, k2, C2, h2⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
