import Benchmarks.Morpho.MetaMorphoV1_1.AccruedSupplySource
import Benchmarks.Morpho.MetaMorphoV1_1.SharesToAssetsDown

/-! Checked share conversion and the accrued-supply helper's tuple return. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def accruedSupplyValue (market : ByteArray) (shares : UInt256) : Value :=
  .tuple [uint256Value (assetsDownWord shares (calldataWord market 0) (calldataWord market 32)),
    uint256Value shares, marketValue market]

def accruedSupplySharesFrame (frame : Frame) (shares : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "shares" (uint256Value shares) }

def accruedSupplyConvertedFrame (frame : Frame) (market : ByteArray) (shares : UInt256) : Frame :=
  { accruedSupplySharesFrame frame shares with
    locals := (accruedSupplySharesFrame frame shares).locals.insert "__c3"
      (uint256Value (assetsDownWord shares (calldataWord market 0) (calldataWord market 32))) }

def accruedSupplyFinalFrame (frame : Frame) (market : ByteArray) (shares : UInt256) : Frame :=
  { accruedSupplyConvertedFrame frame market shares with
    locals := (accruedSupplyConvertedFrame frame market shares).locals.insert "assets"
      (uint256Value (assetsDownWord shares (calldataWord market 0) (calldataWord market 32))) }

theorem accruedSupplySharesPrefix {frame : Frame} {evm : State} {shares : UInt256} {old : Value}
    (hshares : frame.locals.get? "__c2" = some (uint256Value shares))
    (hold : frame.locals.get? "shares" = some old) :
    ABlock config evm frame accruedSupplyTail (accruedSupplySharesFrame frame shares)
      (accruedSupplyTail.drop 1) := by
  constructor
  intro result htail
  exact ExecBlock.consNormal (ExecStmt.assign
    (by simp only [evalExpr?, hshares, EvalResult.ofOption]) (assignLocalValue hold)) htail

theorem accruedSupplyConversionArgs {frame : Frame} {evm : State} {market : ByteArray}
    (shares : UInt256) (hmarket : frame.locals.get? "market" = some (marketValue market)) :
    evalExpr? config (accruedSupplySharesFrame frame shares) evm (.var "shares") =
      .ok (uint256Value shares) ∧
    evalExpr? config (accruedSupplySharesFrame frame shares) evm
        (.field (.var "market") "totalSupplyAssets") = .ok (uint256Value (calldataWord market 0)) ∧
    evalExpr? config (accruedSupplySharesFrame frame shares) evm
        (.field (.var "market") "totalSupplyShares") = .ok (uint256Value (calldataWord market 32)) := by
  have hm : evalExpr? config (accruedSupplySharesFrame frame shares) evm (.var "market") =
      .ok (marketValue market) := by
    simp only [evalExpr?, accruedSupplySharesFrame,
      store_get_ne _ _ (by decide : ("shares" == "market") = false), hmarket, EvalResult.ofOption]
  exact ⟨by simp only [evalExpr?, accruedSupplySharesFrame, store_get_self, EvalResult.ofOption],
    evalExpr_structField hm rfl, evalExpr_structField hm rfl⟩

theorem accruedSupplyTailReverts {frame : Frame} {evm : State} {market : ByteArray}
    {shares : UInt256} {old : Value} (hc : frame.contract = contract)
    (hshares : frame.locals.get? "__c2" = some (uint256Value shares))
    (hold : frame.locals.get? "shares" = some old)
    (hm : frame.locals.get? "market" = some (marketValue market))
    (hbad : ¬ assetsDownFits shares (calldataWord market 0) (calldataWord market 32)) :
    ExecBlock config frame evm accruedSupplyTail .reverted := by
  apply (accruedSupplySharesPrefix hshares hold).run
  rcases frame with ⟨cc, locals, imms⟩
  dsimp only at hc
  subst cc
  have ha := accruedSupplyConversionArgs (evm := evm) shares hm
  exact ExecBlock.consRevert (assetsDownCallReverts _ _ _ _ _ _ _ _ _ _ hbad
    ha.1 ha.2.1 ha.2.2)

theorem accruedSupplyTailReturns {frame : Frame} {evm : State} {market : ByteArray}
    {shares ptr : UInt256} {oldShares oldAssets : Value} (hc : frame.contract = contract)
    (hshares : frame.locals.get? "__c2" = some (uint256Value shares))
    (hs : frame.locals.get? "shares" = some oldShares)
    (ha : frame.locals.get? "assets" = some oldAssets)
    (hm : frame.locals.get? "market" = some (marketValue market))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hfit : assetsDownFits shares (calldataWord market 0) (calldataWord market 32)) :
    ExecBlock config frame evm accruedSupplyTail
      (.returned (accruedSupplyFinalFrame frame market shares) evm
        (some [accruedSupplyValue market shares, uint256Value ptr])) := by
  apply (accruedSupplySharesPrefix hshares hs).run
  rcases frame with ⟨cc, locals, imms⟩
  dsimp only at hc
  subst cc
  have hargs := accruedSupplyConversionArgs (evm := evm) shares hm
  apply ExecBlock.consNormal (assetsDownCall _ _ _ _ _ _ _ _ _ _ hfit
    hargs.1 hargs.2.1 hargs.2.2)
  apply ExecBlock.consNormal (ExecStmt.assign
    (value := uint256Value (assetsDownWord shares (calldataWord market 0) (calldataWord market 32)))
    (by simp only [evalExpr?, store_get_self, EvalResult.ofOption])
    (assignLocalValue (old := oldAssets) (by
      simp only [store_get_ne _ _ (by decide : ("__c3" == "assets") = false),
        store_get_ne _ _ (by decide : ("shares" == "assets") = false), ha])))
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, evalExprList?, accruedSupplyFinalFrame, accruedSupplyConvertedFrame,
    accruedSupplySharesFrame, store_get_self,
    store_get_ne _ _ (by decide : ("assets" == "shares") = false),
    store_get_ne _ _ (by decide : ("__c3" == "shares") = false),
    store_get_ne _ _ (by decide : ("assets" == "market") = false),
    store_get_ne _ _ (by decide : ("__c3" == "market") = false),
    store_get_ne _ _ (by decide : ("shares" == "market") = false),
    store_get_ne _ _ (by decide : ("assets" == cursorName) = false),
    store_get_ne _ _ (by decide : ("__c3" == cursorName) = false),
    store_get_ne _ _ (by decide : ("shares" == cursorName) = false),
    hm, hp, EvalResult.ofOption, pure, bind, EvalResult.bind]
  rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
