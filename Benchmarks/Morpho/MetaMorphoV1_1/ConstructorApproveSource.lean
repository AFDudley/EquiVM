import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorForceApprove

/-! The final constructor call resumes with the approval helper's cursor and unchanged immutables. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false
set_option maxRecDepth 2000

def constructorApprovalArgs : List Expr :=
  [.var "assetAddress", .var "morpho", .intLit (2 ^ 256 - 1)]

theorem constructorApprovalBody : contract.ctor.body.drop 37 =
    cursorCall allocatedForceApproveFunction.name constructorApprovalArgs "approveMorpho" ++ [] := by
  native_decide

theorem constructorApprovalArgs_eval {frame : Frame} {evm : State}
    {asset morpho : AccountAddress} {ptr : UInt256}
    (ha : frame.locals.get? "assetAddress" = some (.address asset))
    (hm : frame.locals.get? "morpho" = some (.address morpho))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr)) :
    evalExprs? config frame evm (constructorApprovalArgs ++ [.var cursorName]) =
      .ok [.address asset, .address morpho, uint256Value constructorApprovalValue, uint256Value ptr] := by
  simp only [constructorApprovalArgs, List.cons_append, List.nil_append, evalExprs?, evalExpr?,
    ha, hm, hp, EvalResult.ofOption, bind, EvalResult.bind, pure,
    constructorApprovalValue, uint256Value, u256_lnot_zero_toNat]
  rfl

theorem constructorApprovalReturns {frame frame' : Frame} {evm evm' : State}
    {asset morpho : AccountAddress} {ptr cursor : UInt256}
    (hc : frame.contract = contract)
    (ha : frame.locals.get? "assetAddress" = some (.address asset))
    (hm : frame.locals.get? "morpho" = some (.address morpho))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hbody : ExecFuncBody config (forceApproveFrame frame.immutables asset morpho constructorApprovalValue ptr)
      evm allocatedForceApproveFunction.body (.returned frame' evm' (some [.tuple [], uint256Value cursor]))) :
    ExecBlock config frame evm (contract.ctor.body.drop 37)
      (.ok (cursorResultFrame frame "approveMorpho" (.tuple []) cursor) evm') := by
  rw [constructorApprovalBody]
  apply cursorCallPrefix (by decide) _ ExecBlock.nil
  apply internalCallFunctionReturn (callee := allocatedForceApproveFunction)
    (value := some [.tuple [], uint256Value cursor])
    (constructorApprovalArgs_eval ha hm hp) (by rw [hc]; rfl) rfl
  simpa only [forceApproveFrame, hc] using hbody

theorem constructorApprovalReverts {frame : Frame} {evm : State}
    {asset morpho : AccountAddress} {ptr : UInt256}
    (hc : frame.contract = contract)
    (ha : frame.locals.get? "assetAddress" = some (.address asset))
    (hm : frame.locals.get? "morpho" = some (.address morpho))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hbody : ExecFuncBody config (forceApproveFrame frame.immutables asset morpho constructorApprovalValue ptr)
      evm allocatedForceApproveFunction.body .reverted) :
    ExecBlock config frame evm (contract.ctor.body.drop 37) .reverted := by
  rw [constructorApprovalBody]
  apply ExecBlock.consRevert
  apply internalCallFunctionRevert (callee := allocatedForceApproveFunction)
    (constructorApprovalArgs_eval ha hm hp) (by rw [hc]; rfl) rfl
  simpa only [forceApproveFrame, hc] using hbody

theorem constructorFinalDecimalsFrame_contract (a : ConstructorArgs) (ok : Bool)
    (out : ByteArray) (I : ExecutionEnv) (strictOut : ByteArray) :
    (constructorFinalDecimalsFrame a ok out I strictOut).contract = contract :=
  constructorMorphoReadyFrame_contract a ok out I

theorem constructorFinalDecimalsFrame_decimals (a : ConstructorArgs) (ok : Bool)
    (out : ByteArray) (I : ExecutionEnv) (strictOut : ByteArray) :
    (constructorFinalDecimalsFrame a ok out I strictOut).locals.get? "assetDecimals" =
      some (uint256Value (calldataWord strictOut 0)) := by
  rw [constructorFinalDecimalsFrame, constructorStrictDecimalsFrame,
    store_get_ne _ _ (by decide), store_get_self]

theorem constructorFinalDecimalsFrame_asset (a : ConstructorArgs) (ok : Bool)
    (out : ByteArray) (I : ExecutionEnv) (strictOut : ByteArray) :
    (constructorFinalDecimalsFrame a ok out I strictOut).locals.get? "assetAddress" = some (.address a.asset) := by
  rw [constructorFinalDecimalsFrame, constructorStrictDecimalsFrame,
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  exact constructorMorphoReadyFrame_asset a ok out I

theorem constructorFinalDecimalsFrame_morpho (a : ConstructorArgs) (ok : Bool)
    (out : ByteArray) (I : ExecutionEnv) (strictOut : ByteArray) :
    (constructorFinalDecimalsFrame a ok out I strictOut).locals.get? "morpho" = some (.address a.morpho) := by
  rw [constructorFinalDecimalsFrame, constructorStrictDecimalsFrame,
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  change (constructorTimelockReadyFrame a ok out I).locals.get? "morpho" = _
  rw [constructorTimelockReadyFrame_preserves a ok out I "morpho"
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  apply Std.HashMap.getElem?_ofList_of_mem (k := "morpho") (by decide) <;> simp

theorem constructorFinalDecimalsFrame_cursor (a : ConstructorArgs) (ok : Bool)
    (out : ByteArray) (I : ExecutionEnv) (strictOut : ByteArray) :
    (constructorFinalDecimalsFrame a ok out I strictOut).locals.get? cursorName =
      some (uint256Value (nextCursor (constructorStrictDecimalsPtr a out) ⟨32⟩)) :=
  store_get_self _ _ _

end Benchmarks.Morpho.MetaMorphoV1_1
