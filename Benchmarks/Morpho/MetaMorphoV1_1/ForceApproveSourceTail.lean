import Benchmarks.Morpho.MetaMorphoV1_1.ForceApproveSourcePrefix

/-! Source statements for the zero-then-maximum approval fallback and final return. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def forceApproveFallbackBody : List Stmt :=
  [reserveBytes 100,
   .internalCall allocatedOptionalReturnFunction.name
     [.var "token", .abiEncodeCall "approve" [.var "spender", .intLit 0], .var cursorName] cursorName,
   .internalCall allocatedOptionalReturnFunction.name
     [.var "token", .var "approvalCall", .var cursorName] cursorName]

def forceApproveCursorFrame (frame : Frame) (ptr : UInt256) : Frame :=
  { frame with locals := frame.locals.insert cursorName (uint256Value ptr) }

structure ForceApproveLocals (frame : Frame) (token spender : AccountAddress)
    (value ptr : UInt256) : Prop where
  contract : frame.contract = MetaMorphoV1_1.contract
  token_eq : frame.locals.get? "token" = some (.address token)
  spender_eq : frame.locals.get? "spender" = some (.address spender)
  data : frame.locals.get? "approvalCall" = some (.bytes (constructorApproveCalldata spender value))
  cursor : frame.locals.get? cursorName = some (uint256Value ptr)

theorem ForceApproveLocals.setCursor {frame : Frame} {token spender : AccountAddress}
    {value ptr : UInt256} (h : ForceApproveLocals frame token spender value ptr) (next : UInt256) :
    ForceApproveLocals (forceApproveCursorFrame frame next) token spender value next := by
  refine ⟨h.contract, ?_, ?_, ?_, store_get_self _ _ _⟩
  · exact (store_get_ne _ _ (by decide : (cursorName == "token") = false)).trans h.token_eq
  · exact (store_get_ne _ _ (by decide : (cursorName == "spender") = false)).trans h.spender_eq
  · exact (store_get_ne _ _ (by decide : (cursorName == "approvalCall") = false)).trans h.data

theorem forceApproveReadyLocals (imms : Store) (token spender : AccountAddress)
    (value ptr : UInt256) (flag : Bool) (cursor : UInt256) :
    ForceApproveLocals (forceApproveReadyFrame imms token spender value ptr flag cursor)
      token spender value cursor := by
  constructor
  · rfl
  all_goals simp [forceApproveReadyFrame, forceApproveFlagFrame, forceApproveProbeFrame,
    forceApproveAllocatedFrame, forceApproveDataFrame, forceApproveFrame,
    cursorName, slotsAndCursorName, Std.HashMap.getElem_insert]

theorem forceApproveReserve {frame : Frame} {evm : State} {token spender : AccountAddress}
    {value ptr : UInt256} (h : ForceApproveLocals frame token spender value ptr)
    (hfit : allocationFits ptr ⟨100⟩) :
    ExecStmt config frame evm (reserveBytes 100)
      (.ok (forceApproveCursorFrame frame (nextCursor ptr ⟨100⟩)) evm) :=
  allocateCallReturns cursorName (by rw [h.contract]; exact allocateFunction_lookup)
    (by simp only [evalExpr?, h.cursor, EvalResult.ofOption])
    (by simp [evalExpr?, pure, uint256Value]; decide) hfit

theorem forceApproveReserveReverts {frame : Frame} {evm : State} {token spender : AccountAddress}
    {value ptr : UInt256} (h : ForceApproveLocals frame token spender value ptr)
    (hbad : ¬ allocationFits ptr ⟨100⟩) : ExecStmt config frame evm (reserveBytes 100) .reverted :=
  allocateCallReverts cursorName (by rw [h.contract]; exact allocateFunction_lookup)
    (by simp only [evalExpr?, h.cursor, EvalResult.ofOption])
    (by simp [evalExpr?, pure, uint256Value]; decide) hbad

def forceApproveCallArgs (zero : Bool) : List Expr :=
  [.var "token", if zero then .abiEncodeCall "approve" [.var "spender", .intLit 0]
    else .var "approvalCall", .var cursorName]

theorem forceApproveCallArgs_eval {frame : Frame} {evm : State} {token spender : AccountAddress}
    {value ptr : UInt256} (h : ForceApproveLocals frame token spender value ptr) (zero : Bool) :
    evalExprs? config frame evm (forceApproveCallArgs zero) =
      .ok [.address token, .bytes (constructorApproveCalldata spender (if zero then ⟨0⟩ else value)),
        uint256Value ptr] := by
  cases zero with
  | false => simp only [forceApproveCallArgs, Bool.false_eq_true, if_false, evalExprs?, evalExpr?,
      h.token_eq, h.data, h.cursor, EvalResult.ofOption, bind, EvalResult.bind, pure]
  | true =>
      have he : evalExpr? config frame evm (.abiEncodeCall "approve" [.var "spender", .intLit 0]) =
          .ok (.bytes (constructorApproveCalldata spender ⟨0⟩)) := by
        simp only [evalExprList?, evalExpr?, h.spender_eq, EvalResult.ofOption, bind, EvalResult.bind, pure]
        have he := constructorApproveEncode spender ⟨0⟩
        change config.externalABI.encode? "approve" [.address spender, .int 0] =
          some (constructorApproveCalldata spender ⟨0⟩) at he
        rw [he]
      simp only [forceApproveCallArgs, if_true, evalExprs?, he, evalExpr?, h.token_eq, h.cursor,
        EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem forceApproveOptionalCall {frame frame' : Frame} {evm evm' : State}
    {token spender : AccountAddress} {value ptr cursor : UInt256}
    (h : ForceApproveLocals frame token spender value ptr) (zero : Bool)
    (hcall : ExecFuncBody config
      (optionalCallFrame frame.immutables token (constructorApproveCalldata spender (if zero then ⟨0⟩ else value)) ptr)
      evm allocatedOptionalReturnFunction.body (.returned frame' evm' (some [uint256Value cursor]))) :
    ExecStmt config frame evm
      (.internalCall allocatedOptionalReturnFunction.name (forceApproveCallArgs zero) cursorName)
      (.ok (forceApproveCursorFrame frame cursor) evm') := by
  apply internalCallFunctionReturn (callee := allocatedOptionalReturnFunction)
    (value := some [uint256Value cursor]) (calleeStele := frame') (calleeEvm := evm')
    (forceApproveCallArgs_eval h zero) (by rw [h.contract]; rfl) rfl
  simpa only [optionalCallFrame, h.contract] using hcall

theorem forceApproveOptionalCallReverts {frame : Frame} {evm : State}
    {token spender : AccountAddress} {value ptr : UInt256}
    (h : ForceApproveLocals frame token spender value ptr) (zero : Bool)
    (hcall : ExecFuncBody config
      (optionalCallFrame frame.immutables token (constructorApproveCalldata spender (if zero then ⟨0⟩ else value)) ptr)
      evm allocatedOptionalReturnFunction.body .reverted) :
    ExecStmt config frame evm
      (.internalCall allocatedOptionalReturnFunction.name (forceApproveCallArgs zero) cursorName) .reverted := by
  apply internalCallFunctionRevert (callee := allocatedOptionalReturnFunction)
    (forceApproveCallArgs_eval h zero) (by rw [h.contract]; rfl) rfl
  simpa only [optionalCallFrame, h.contract] using hcall

theorem forceApproveTailBody : allocatedForceApproveFunction.body.drop 5 =
    [.ite (.unary .not (.var "__c0")) forceApproveFallbackBody [],
     .return [.tupleLit [], .var cursorName]] := rfl

theorem forceApproveReadyCondition (evm : State) (imms : Store) (token spender : AccountAddress)
    (value ptr : UInt256) (flag : Bool) (cursor : UInt256) :
    evalExpr? config (forceApproveReadyFrame imms token spender value ptr flag cursor) evm
      (.unary .not (.var "__c0")) = .ok (.bool (!flag)) := by
  simp [evalExpr?, forceApproveReadyFrame, forceApproveFlagFrame, cursorName,
    Std.HashMap.getElem_insert, EvalResult.ofOption, bind, EvalResult.bind, evalUnaryOp?]

theorem forceApproveReturn {frame : Frame} {evm : State} {cursor : UInt256}
    (hc : frame.locals.get? cursorName = some (uint256Value cursor)) :
    ExecBlock config frame evm [.return [.tupleLit [], .var cursorName]]
      (.returned frame evm (some [.tuple [], uint256Value cursor])) := by
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, evalExprList?, hc, EvalResult.ofOption,
    bind, EvalResult.bind, pure]

theorem forceApproveTailDirect (evm : State) (imms : Store) (token spender : AccountAddress)
    (value ptr cursor : UInt256) :
    ExecBlock config (forceApproveReadyFrame imms token spender value ptr true cursor) evm
      (allocatedForceApproveFunction.body.drop 5)
      (.returned (forceApproveReadyFrame imms token spender value ptr true cursor) evm
        (some [.tuple [], uint256Value cursor])) := by
  rw [forceApproveTailBody]
  apply ExecBlock.consNormal (ExecStmt.iteFalse (forceApproveReadyCondition ..) ExecBlock.nil)
  exact forceApproveReturn (forceApproveReadyLocals imms token spender value ptr true cursor).cursor

theorem forceApproveTailFallback {evm evm' : State} (imms : Store) (token spender : AccountAddress)
    (value ptr cursor cursor' : UInt256) {frame' : Frame}
    (hfall : ExecBlock config (forceApproveReadyFrame imms token spender value ptr false cursor) evm
      forceApproveFallbackBody (.ok frame' evm'))
    (hc : frame'.locals.get? cursorName = some (uint256Value cursor')) :
    ExecBlock config (forceApproveReadyFrame imms token spender value ptr false cursor) evm
      (allocatedForceApproveFunction.body.drop 5)
      (.returned frame' evm' (some [.tuple [], uint256Value cursor'])) := by
  rw [forceApproveTailBody]
  exact ExecBlock.consNormal (ExecStmt.iteTrue (forceApproveReadyCondition ..) hfall)
    (forceApproveReturn hc)

theorem forceApproveTailReverts (evm : State) (imms : Store) (token spender : AccountAddress)
    (value ptr cursor : UInt256)
    (hfall : ExecBlock config (forceApproveReadyFrame imms token spender value ptr false cursor) evm
      forceApproveFallbackBody .reverted) :
    ExecBlock config (forceApproveReadyFrame imms token spender value ptr false cursor) evm
      (allocatedForceApproveFunction.body.drop 5) .reverted := by
  rw [forceApproveTailBody]
  exact ExecBlock.consRevert (ExecStmt.iteTrue (forceApproveReadyCondition ..) hfall)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
