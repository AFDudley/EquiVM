import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawMorphoLoopState
import Benchmarks.Morpho.MetaMorphoV1_1.AccruedSupplySource
import Benchmarks.Morpho.MetaMorphoV1_1.AccruedSupplyTailSource

/-! Source call boundaries and tuple projections for the withdrawal readers. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem accruedSupplyReaderCall {evm evm' : State} {locals imms : Store}
    {p : MarketParamsData} {id ptr : UInt256} {args : List Expr} {ret : Ident}
    {final : Frame} {values : Option (List Value)}
    (hargs : evalExprs? config { contract := contract, locals := locals, immutables := imms }
      evm args = .ok [p.value, wordBytes32Value id, uint256Value ptr])
    (hbody : ExecFuncBody config (accruedSupplyFrame imms p id ptr)
      evm allocatedAccruedSupplyBalanceFunction.body (.returned final evm' values)) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall allocatedAccruedSupplyBalanceFunction.name args ret)
      (.ok (resumeAfterInternalCall
        { contract := contract, locals := locals, immutables := imms } ret values) evm') :=
  internalCallFunctionReturn (callee := allocatedAccruedSupplyBalanceFunction) hargs
    allocatedAccruedSupplyBalanceFunction_lookup rfl hbody

theorem accruedSupplyReaderRevert {evm : State} {locals imms : Store}
    {p : MarketParamsData} {id ptr : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config { contract := contract, locals := locals, immutables := imms }
      evm args = .ok [p.value, wordBytes32Value id, uint256Value ptr])
    (hbody : ExecFuncBody config (accruedSupplyFrame imms p id ptr)
      evm allocatedAccruedSupplyBalanceFunction.body .reverted) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall allocatedAccruedSupplyBalanceFunction.name args ret) .reverted :=
  internalCallFunctionRevert (callee := allocatedAccruedSupplyBalanceFunction) hargs
    allocatedAccruedSupplyBalanceFunction_lookup rfl hbody

def withdrawMorphoBalancesFrame (frame : Frame) (market : ByteArray) (shares : UInt256) : Frame :=
  { frame with locals := (frame.locals.insert "supplyAssets" (uint256Value (
      assetsDownWord shares (calldataWord market 0) (calldataWord market 32)))).insert "market" (marketValue market) }

theorem withdrawMorphoBalancesSource {frame : Frame} {evm : State}
    {market : ByteArray} {shares : UInt256}
    (h : frame.locals.get? "__c1" = some (accruedSupplyValue market shares)) :
    ExecBlock config frame evm withdrawMorphoBalances
      (.ok (withdrawMorphoBalancesFrame frame market shares) evm) := by
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value
    (assetsDownWord shares (calldataWord market 0) (calldataWord market 32))) ?_) ?_
  · simp only [evalExpr?, h, EvalResult.ofOption, accruedSupplyValue, tupleGetValue?,
      bind, EvalResult.bind, List.getElem?_cons_zero]
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := marketValue market) ?_) ExecBlock.nil
  simp only [evalExpr?, store_get_ne _ _ (by decide : ("supplyAssets" == "__c1") = false),
    h, EvalResult.ofOption, accruedSupplyValue, tupleGetValue?, bind, EvalResult.bind,
    List.getElem?_cons_succ, List.getElem?_cons_zero]

theorem WithdrawMorphoLocals.balances {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i assets cursor : UInt256} (h : WithdrawMorphoLocals v frame i assets cursor)
    (market : ByteArray) (shares : UInt256) :
    WithdrawMorphoLocals v (withdrawMorphoBalancesFrame frame market shares) i assets cursor :=
  (h.insert "supplyAssets" _ (by decide) (by decide) (by decide) (by decide) (by decide)).insert
    "market" _ (by decide) (by decide) (by decide) (by decide) (by decide)

theorem withdrawMorphoBalancesFrame_preserves (frame : Frame) (market : ByteArray)
    (shares : UInt256) (name : Ident) (hm : ("market" == name) = false)
    (ha : ("supplyAssets" == name) = false) :
    (withdrawMorphoBalancesFrame frame market shares).locals.get? name = frame.locals.get? name := by
  simp only [withdrawMorphoBalancesFrame, store_get_ne _ _ hm, store_get_ne _ _ ha]

theorem withdrawMorphoBalancesFrame_assets (frame : Frame) (market : ByteArray) (shares : UInt256) :
    (withdrawMorphoBalancesFrame frame market shares).locals.get? "supplyAssets" = some
      (uint256Value (assetsDownWord shares (calldataWord market 0) (calldataWord market 32))) := by
  simp only [withdrawMorphoBalancesFrame,
    store_get_ne _ _ (by decide : ("market" == "supplyAssets") = false), store_get_self]

theorem withdrawMorphoBalancesFrame_market (frame : Frame) (market : ByteArray) (shares : UInt256) :
    (withdrawMorphoBalancesFrame frame market shares).locals.get? "market" = some (marketValue market) :=
  store_get_self _ _ _

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
