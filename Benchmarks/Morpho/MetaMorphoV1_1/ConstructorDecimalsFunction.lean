import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDecimalsSource

/-! The allocated source helper for the constructor's optional decimals call. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false
set_option maxRecDepth 2000

def constructorDecimalsFrame (imms : Store) (asset : AccountAddress) (ptr : UInt256) : Frame :=
  ⟨contract, ((∅ : Store).insert cursorName (uint256Value ptr)).insert "asset_" (.address asset), imms⟩

def constructorDecimalsRequestFrame (imms : Store) (asset : AccountAddress) (ptr : UInt256) : Frame :=
  { constructorDecimalsFrame imms asset ptr with
    locals := (constructorDecimalsFrame imms asset ptr).locals.insert cursorName
      (uint256Value (nextCursor ptr ⟨36⟩)) }

def constructorDecimalsRawFrame (imms : Store) (asset : AccountAddress) (ptr : UInt256)
    (ok : Bool) (out : ByteArray) : Frame :=
  { constructorDecimalsRequestFrame imms asset ptr with
    locals := ((constructorDecimalsRequestFrame imms asset ptr).locals.insert "success" (.bool ok)).insert
      "encodedDecimals" (.bytes out) }

def constructorDecimalsDataFrame (imms : Store) (asset : AccountAddress) (ptr : UInt256)
    (ok : Bool) (out : ByteArray) : Frame :=
  { constructorDecimalsRawFrame imms asset ptr ok out with
    locals := (constructorDecimalsRawFrame imms asset ptr ok out).locals.insert "returndata" (.bytes out) }

theorem allocatedTryGetAssetDecimals_lookup :
    lookupCallable? contract allocatedTryGetAssetDecimalsFunction.name =
      some allocatedTryGetAssetDecimalsFunction.toCallable := rfl

theorem constructorDecimalsFrame_cursor (imms : Store) (asset : AccountAddress) (ptr : UInt256)
    (evm : State) :
    evalExpr? config (constructorDecimalsFrame imms asset ptr) evm (.var cursorName) =
      .ok (uint256Value ptr) := by
  simp only [evalExpr?, constructorDecimalsFrame,
    store_get_ne _ _ (show ("asset_" == cursorName) = false by decide), store_get_self,
    EvalResult.ofOption]

theorem constructorDecimalsDataFrame_cursor (imms : Store) (asset : AccountAddress) (ptr : UInt256)
    (ok : Bool) (out : ByteArray) :
    (constructorDecimalsDataFrame imms asset ptr ok out).locals.get? cursorName =
      some (uint256Value (nextCursor ptr ⟨36⟩)) := by
  simp [constructorDecimalsDataFrame, constructorDecimalsRawFrame, constructorDecimalsRequestFrame,
    cursorName, Std.HashMap.getElem_insert]

theorem constructorDecimalsSourcePrefix {evm evm' : State} (imms : Store) (asset : AccountAddress)
    (ptr : UInt256) (ok : Bool) (out : ByteArray) {result : ExecResult}
    (hfit : allocationFits ptr ⟨36⟩)
    (hcall : typedCallViaEVM config evm asset "decimals" 0 [] (ok, evm', out) false)
    (htail : ExecBlock config (constructorDecimalsDataFrame imms asset ptr ok out) evm'
      (reserveCallReturn :: constructorDecimalsReturnTail) result) :
    ExecBlock config (constructorDecimalsFrame imms asset ptr) evm
      allocatedTryGetAssetDecimalsFunction.body result := by
  rw [allocatedTryGetAssetDecimals_body]
  apply ExecBlock.consNormal (allocateCallReturns cursorName allocateFunction_lookup
    (constructorDecimalsFrame_cursor imms asset ptr evm)
    (by simp only [evalExpr?, pure]; rfl) hfit)
  have hr : evalExpr? config (constructorDecimalsRequestFrame imms asset ptr) evm (.var "asset_") =
      .ok (.address asset) := by
    simp [evalExpr?, constructorDecimalsRequestFrame, constructorDecimalsFrame, cursorName,
      Std.HashMap.getElem_insert, EvalResult.ofOption]
  obtain ⟨data, he, hraw⟩ := hcall
  have hd : evalExpr? config (constructorDecimalsRequestFrame imms asset ptr) evm
      (.abiEncodeCall "decimals" []) = .ok (.bytes data) := by
    simp only [evalExpr?, evalExprList?, bind, EvalResult.bind, pure, he]
    rfl
  have ha : EVM.address asset.val = asset := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt asset.isLt
  rw [← ha] at hraw
  have hstep : ExecStmt config (constructorDecimalsRequestFrame imms asset ptr) evm
      (.lowLevelCall (.var "asset_") (.intLit 0) (.abiEncodeCall "decimals" [])
        "success" "encodedDecimals" false)
      (.ok (constructorDecimalsRawFrame imms asset ptr ok out) evm') := by
    cases ok with
    | false => exact ExecStmt.lowLevelCallFailure hr (by simp only [evalExpr?, pure]) hd hraw
    | true => exact ExecStmt.lowLevelCallSuccess hr (by simp only [evalExpr?, pure]) hd hraw
  apply ExecBlock.consNormal hstep
  apply ExecBlock.consNormal (ExecStmt.letDecl ?_) htail
  simp only [evalExpr?, constructorDecimalsRawFrame, store_get_self, EvalResult.ofOption]

theorem constructorDecimalsBodyReturns {evm evm' : State} (imms : Store) (asset : AccountAddress)
    (ptr : UInt256) (ok : Bool) (out : ByteArray)
    (hfit : allocationFits ptr ⟨36⟩)
    (hcall : typedCallViaEVM config evm asset "decimals" 0 [] (ok, evm', out) false)
    (hreturn : callReturnFits (nextCursor ptr ⟨36⟩) out) :
    ∃ frame', ExecFuncBody config (constructorDecimalsFrame imms asset ptr) evm
      allocatedTryGetAssetDecimalsFunction.body
      (.returned frame' evm' (some [constructorDecimalsValue ok out,
        uint256Value (callReturnCursor (nextCursor ptr ⟨36⟩) out)])) := by
  have hp := constructorDecimalsDataFrame_cursor imms asset ptr ok out
  have hsize : out.size < 2 ^ 255 := by rcases hreturn with hz | ⟨hs, _⟩ <;> omega
  obtain ⟨frame', htail⟩ := constructorDecimalsTailSource (evm := evm') (ok := ok) (out := out)
    (frame := callReturnFrame (constructorDecimalsDataFrame imms asset ptr ok out)
      (nextCursor ptr ⟨36⟩) out)
    (by
      rw [callReturnFrame_get _ _ _ _ (show (cursorName == "success") = false by decide)]
      simp [constructorDecimalsDataFrame, constructorDecimalsRawFrame, Std.HashMap.getElem_insert])
    (by
      rw [callReturnFrame_get _ _ _ _ (show (cursorName == "encodedDecimals") = false by decide)]
      simp [constructorDecimalsDataFrame, constructorDecimalsRawFrame, Std.HashMap.getElem_insert])
    (callReturnFrame_cursor _ _ out hp) hsize
  refine ⟨frame', ExecFuncBody.execBlockRet ?_⟩
  apply constructorDecimalsSourcePrefix imms asset ptr ok out hfit hcall
  exact ExecBlock.consNormal
    (reserveCallReturnReturns allocateFunction_lookup hp (store_get_self _ _ _) hreturn) htail

theorem constructorDecimalsBodyRequestReverts (imms : Store) (asset : AccountAddress)
    (ptr : UInt256) (evm : State) (hfit : ¬ allocationFits ptr ⟨36⟩) :
    ExecFuncBody config (constructorDecimalsFrame imms asset ptr) evm
      allocatedTryGetAssetDecimalsFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [allocatedTryGetAssetDecimals_body]
  exact ExecBlock.consRevert (allocateCallReverts cursorName allocateFunction_lookup
    (constructorDecimalsFrame_cursor imms asset ptr evm)
    (by simp only [evalExpr?, pure]; rfl) hfit)

theorem constructorDecimalsBodyReturnReverts {evm evm' : State} (imms : Store) (asset : AccountAddress)
    (ptr : UInt256) (ok : Bool) (out : ByteArray)
    (hfit : allocationFits ptr ⟨36⟩)
    (hcall : typedCallViaEVM config evm asset "decimals" 0 [] (ok, evm', out) false)
    (hreturn : ¬ callReturnFits (nextCursor ptr ⟨36⟩) out) :
    ExecFuncBody config (constructorDecimalsFrame imms asset ptr) evm
      allocatedTryGetAssetDecimalsFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply constructorDecimalsSourcePrefix imms asset ptr ok out hfit hcall
  exact ExecBlock.consRevert (reserveCallReturnReverts allocateFunction_lookup
    (constructorDecimalsDataFrame_cursor imms asset ptr ok out) (store_get_self _ _ _) hreturn)

theorem constructorDecimalsStatementReturns {evm evm' : State} (locals imms : Store)
    (asset : AccountAddress) (ptr : UInt256) (ok : Bool) (out : ByteArray)
    (args : List Expr) (retVar : Ident)
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address asset, uint256Value ptr])
    (hfit : allocationFits ptr ⟨36⟩)
    (hcall : typedCallViaEVM config evm asset "decimals" 0 [] (ok, evm', out) false)
    (hreturn : callReturnFits (nextCursor ptr ⟨36⟩) out) :
    ExecStmt config ⟨contract, locals, imms⟩ evm
      (.internalCall allocatedTryGetAssetDecimalsFunction.name args retVar)
      (.ok ⟨contract, locals.insert retVar (.tuple [constructorDecimalsValue ok out,
        uint256Value (callReturnCursor (nextCursor ptr ⟨36⟩) out)]), imms⟩ evm') := by
  obtain ⟨frame', hbody⟩ := constructorDecimalsBodyReturns imms asset ptr ok out hfit hcall hreturn
  exact internalCallFunctionReturn (callee := allocatedTryGetAssetDecimalsFunction)
    hargs allocatedTryGetAssetDecimals_lookup rfl hbody

theorem constructorDecimalsStatementRequestReverts (evm : State) (locals imms : Store)
    (asset : AccountAddress) (ptr : UInt256) (args : List Expr) (retVar : Ident)
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address asset, uint256Value ptr]) (hfit : ¬ allocationFits ptr ⟨36⟩) :
    ExecStmt config ⟨contract, locals, imms⟩ evm
      (.internalCall allocatedTryGetAssetDecimalsFunction.name args retVar) .reverted :=
  internalCallFunctionRevert (callee := allocatedTryGetAssetDecimalsFunction)
    hargs allocatedTryGetAssetDecimals_lookup rfl
    (constructorDecimalsBodyRequestReverts imms asset ptr evm hfit)

theorem constructorDecimalsStatementReturnReverts {evm evm' : State} (locals imms : Store)
    (asset : AccountAddress) (ptr : UInt256) (ok : Bool) (out : ByteArray)
    (args : List Expr) (retVar : Ident)
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address asset, uint256Value ptr]) (hfit : allocationFits ptr ⟨36⟩)
    (hcall : typedCallViaEVM config evm asset "decimals" 0 [] (ok, evm', out) false)
    (hreturn : ¬ callReturnFits (nextCursor ptr ⟨36⟩) out) :
    ExecStmt config ⟨contract, locals, imms⟩ evm
      (.internalCall allocatedTryGetAssetDecimalsFunction.name args retVar) .reverted :=
  internalCallFunctionRevert (callee := allocatedTryGetAssetDecimalsFunction)
    hargs allocatedTryGetAssetDecimals_lookup rfl
    (constructorDecimalsBodyReturnReverts imms asset ptr ok out hfit hcall hreturn)

end Benchmarks.Morpho.MetaMorphoV1_1
