import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateBalancesSource
import Benchmarks.Morpho.MetaMorphoV1_1.AccruedSupplySimulation
import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawMorphoReadersSource
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_032

/-! The accrued-balance call for a decoded row, retaining its actual post-call state. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem reallocateAccruedSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {values : List Value} {mem row : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr allocation params id i supplied withdrawn : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 24 ≤ 1024)
    (hl : ReallocateLocals v frame values i supplied withdrawn ptr)
    (hrow : frame.locals.get? "allocation" = some (reallocateAllocationValue row))
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hparams : memLoad allocation mem = params)
    (hparamslo : 96 ≤ params.toNat) (hspan : params.toNat + 160 ≤ ptr.toNat)
    (hmem : params.toNat + 160 ≤ mem.size)
    (hloads : MarketParamsLoads mem params (marketParamsData row))
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨6152⟩
      ((allocation + ⟨32⟩) :: allocation :: withdrawn :: id :: R) mem aw rdata σ k C) :
    (ExecBlock config frame evm (reallocateRowAccrued ++ reallocateRowBalances) .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (market : ByteArray) (shares : UInt256)
      (result : AccruedSupplyMarketResult mem ptr market) (out : ByteArray)
      (aw' : UInt256) (k' C' : Nat),
      SourceState s0 I evm'.accountMap evm' ∧
      ReallocateLocals v frame' values i supplied withdrawn result.cursor ∧
      frame'.locals.get? "allocation" = some (reallocateAllocationValue row) ∧
      frame'.locals.get? "id" = some (wordBytes32Value id) ∧
      frame'.locals.get? "supplyAssets" = some (uint256Value
        (assetsDownWord shares (calldataWord market 0) (calldataWord market 32))) ∧
      frame'.locals.get? "supplyShares" = some (uint256Value shares) ∧
      ExecBlock config frame evm (reallocateRowAccrued ++ reallocateRowBalances) (.ok frame' evm') ∧
      RD (deployedRuntime v) I g s0 ⟨6162⟩
        (result.marketPtr :: shares :: assetsDownWord shares (calldataWord market 0)
          (calldataWord market 32) :: (allocation + ⟨32⟩) :: allocation :: withdrawn :: id :: R)
        result.memory aw' out evm'.accountMap k' C' := by
  rcases frame with ⟨c, locals, imms⟩
  have hc := hl.contract
  have himms := hl.imms
  dsimp only at hc himms
  subst c
  subst imms
  let frame : Frame := { contract := contract, locals := locals, immutables := immStore v }
  have hcursor : frame.locals.get? cursorName = some (uint256Value ptr) := hl.cursor
  have heparams := reallocateAllocationParams (evm := evm) hrow
  have hargs : evalExprs? config frame evm
      [.field (.var "allocation") "marketParams", .var "id", .var cursorName] =
      .ok [(marketParamsData row).value, wordBytes32Value id, uint256Value ptr] := by
    dsimp only [frame] at hcursor ⊢
    simp only [evalExprs?, heparams, evalExpr?, hid, hcursor,
      EvalResult.ofOption, bind, EvalResult.bind, pure]
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_6152_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [metaMorphoV1_1_block_6152_stack, hparams] at h1
  rcases accruedSupplySimulation v (marketParamsData row)
      (by simp only [List.length_cons]; omega) hcalldata hfree hlo hparamslo hspan hmem hloads hs
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1 with
    ⟨hbad, hrev⟩ | ⟨evm', final, market, shares, result, out, aw2, k2, C2,
      hs', _, hbody, h2⟩
  · exact .inl ⟨ExecBlock.consRevert (accruedSupplyReaderRevert hargs hbad), hrev⟩
  have hcall := accruedSupplyReaderCall (ret := slotsAndCursorName) hargs hbody
  let frame1 := cursorResultFrame frame "__c3" (accruedSupplyValue market shares) result.cursor
  let frame2 := reallocateBalancesFrame frame1 market shares
  have hl1 : ReallocateLocals v frame1 values i supplied withdrawn result.cursor :=
    hl.reader _ _ _ (by decide)
  have hc3 : frame1.locals.get? "__c3" = some (accruedSupplyValue market shares) :=
    cursorResultFrame_value _ _ _ _ (by decide)
  have hbalances := reallocateBalancesSource (evm := evm') hc3
  refine .inr ⟨evm', frame2, market, shares, result, out, aw2, k2, C2, hs',
    hl1.balances market shares, ?_, ?_, reallocateBalancesFrame_assets _ _ _,
      reallocateBalancesFrame_shares _ _ _, cursorCallPrefix (by decide) hcall hbalances, h2⟩
  · rw [reallocateBalancesFrame_preserves _ _ _ _ (by decide) (by decide),
      cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact hrow
  · rw [reallocateBalancesFrame_preserves _ _ _ _ (by decide) (by decide),
      cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact hid

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
