import Benchmarks.Morpho.MetaMorphoV1_1.OptionalBoolCallSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorApproveABI

/-! Allocate the maximum approval request and carry the probe's Boolean and cursor to forceApprove. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def forceApproveFrame (imms : Store) (token spender : AccountAddress) (value ptr : UInt256) : Frame :=
  ⟨contract, ((((∅ : Store).insert cursorName (uint256Value ptr)).insert
    "value" (uint256Value value)).insert "spender" (.address spender)).insert "token" (.address token), imms⟩

def forceApproveDataFrame (imms : Store) (token spender : AccountAddress) (value ptr : UInt256) : Frame :=
  { forceApproveFrame imms token spender value ptr with
    locals := (forceApproveFrame imms token spender value ptr).locals.insert "approvalCall"
      (.bytes (constructorApproveCalldata spender value)) }

def forceApproveAllocatedFrame (imms : Store) (token spender : AccountAddress) (value ptr : UInt256) : Frame :=
  { forceApproveDataFrame imms token spender value ptr with
    locals := (forceApproveDataFrame imms token spender value ptr).locals.insert cursorName
      (uint256Value (nextCursor ptr ⟨100⟩)) }

def forceApproveProbeFrame (imms : Store) (token spender : AccountAddress)
    (value ptr : UInt256) (flag : Bool) (cursor : UInt256) : Frame :=
  { forceApproveAllocatedFrame imms token spender value ptr with
    locals := (forceApproveAllocatedFrame imms token spender value ptr).locals.insert slotsAndCursorName
      (.tuple [.bool flag, uint256Value cursor]) }

def forceApproveFlagFrame (imms : Store) (token spender : AccountAddress)
    (value ptr : UInt256) (flag : Bool) (cursor : UInt256) : Frame :=
  { forceApproveProbeFrame imms token spender value ptr flag cursor with
    locals := (forceApproveProbeFrame imms token spender value ptr flag cursor).locals.insert "__c0" (.bool flag) }

def forceApproveReadyFrame (imms : Store) (token spender : AccountAddress)
    (value ptr : UInt256) (flag : Bool) (cursor : UInt256) : Frame :=
  { forceApproveFlagFrame imms token spender value ptr flag cursor with
    locals := (forceApproveFlagFrame imms token spender value ptr flag cursor).locals.insert cursorName
      (uint256Value cursor) }

theorem forceApproveEncodeSource (evm : State) (imms : Store) (token spender : AccountAddress)
    (value ptr : UInt256) :
    evalExpr? config (forceApproveFrame imms token spender value ptr) evm
      (.abiEncodeCall "approve" [.var "spender", .var "value"]) =
      .ok (.bytes (constructorApproveCalldata spender value)) := by
  simp [evalExpr?, evalExprList?, forceApproveFrame, Std.HashMap.getElem_insert,
    EvalResult.ofOption, bind, EvalResult.bind, pure, constructorApproveEncode]

theorem forceApproveCursorSource (evm : State) (imms : Store) (token spender : AccountAddress)
    (value ptr : UInt256) :
    evalExpr? config (forceApproveDataFrame imms token spender value ptr) evm
      (.var cursorName) = .ok (uint256Value ptr) := by
  simp [evalExpr?, forceApproveDataFrame, forceApproveFrame, cursorName,
    Std.HashMap.getElem_insert, EvalResult.ofOption]

theorem forceApproveProbeArgs (evm : State) (imms : Store) (token spender : AccountAddress)
    (value ptr : UInt256) :
    evalExprs? config (forceApproveAllocatedFrame imms token spender value ptr) evm
      [.var "token", .var "approvalCall", .var cursorName] =
      .ok [.address token, .bytes (constructorApproveCalldata spender value),
        uint256Value (nextCursor ptr ⟨100⟩)] := by
  simp [evalExprs?, evalExpr?, forceApproveAllocatedFrame, forceApproveDataFrame,
    forceApproveFrame, cursorName, Std.HashMap.getElem_insert, EvalResult.ofOption,
    bind, EvalResult.bind, pure]

theorem forceApproveAllocatePrefix (evm : State) (imms : Store) (token spender : AccountAddress)
    (value ptr : UInt256) {result : ExecResult} (hfit : allocationFits ptr ⟨100⟩)
    (htail : ExecBlock config (forceApproveAllocatedFrame imms token spender value ptr) evm
      (allocatedForceApproveFunction.body.drop 2) result) :
    ExecBlock config (forceApproveFrame imms token spender value ptr) evm
      allocatedForceApproveFunction.body result := by
  apply ExecBlock.consNormal (ExecStmt.letDecl (forceApproveEncodeSource evm imms token spender value ptr))
  apply ExecBlock.consNormal _ htail
  exact allocateCallReturns cursorName allocateFunction_lookup
    (forceApproveCursorSource evm imms token spender value ptr)
    (by simp [evalExpr?, pure, uint256Value]; decide) hfit

theorem forceApproveProbePrefix {evm evm' : State} (imms : Store) (token spender : AccountAddress)
    (value ptr : UInt256) (flag : Bool) (cursor : UInt256) {frame' : Frame} {result : ExecResult}
    (hfit : allocationFits ptr ⟨100⟩)
    (hprobe : ExecFuncBody config
      (optionalCallFrame imms token (constructorApproveCalldata spender value) (nextCursor ptr ⟨100⟩))
      evm allocatedOptionalReturnBoolFunction.body
      (.returned frame' evm' (some [.bool flag, uint256Value cursor])))
    (htail : ExecBlock config (forceApproveReadyFrame imms token spender value ptr flag cursor) evm'
      (allocatedForceApproveFunction.body.drop 5) result) :
    ExecBlock config (forceApproveFrame imms token spender value ptr) evm
      allocatedForceApproveFunction.body result := by
  apply forceApproveAllocatePrefix evm imms token spender value ptr hfit
  apply ExecBlock.consNormal (internalCallFunctionReturn (callee := allocatedOptionalReturnBoolFunction)
    (forceApproveProbeArgs evm imms token spender value ptr) rfl rfl hprobe)
  apply ExecBlock.consNormal (ExecStmt.letDecl ?_)
  · apply ExecBlock.consNormal (ExecStmt.letDecl ?_) htail
    change evalExpr? config (forceApproveFlagFrame imms token spender value ptr flag cursor) evm' _ = _
    simp [evalExpr?, forceApproveFlagFrame, forceApproveProbeFrame, slotsAndCursorName,
      Std.HashMap.getElem_insert, EvalResult.ofOption, bind, EvalResult.bind, tupleGetValue?]
  · change evalExpr? config (forceApproveProbeFrame imms token spender value ptr flag cursor) evm' _ = _
    simp only [evalExpr?, forceApproveProbeFrame, store_get_self, EvalResult.ofOption,
      bind, EvalResult.bind, tupleGetValue?]
    rfl

theorem forceApproveRevertsAllocation (evm : State) (imms : Store) (token spender : AccountAddress)
    (value ptr : UInt256) (hbad : ¬ allocationFits ptr ⟨100⟩) :
    ExecFuncBody config (forceApproveFrame imms token spender value ptr) evm
      allocatedForceApproveFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consNormal (ExecStmt.letDecl (forceApproveEncodeSource evm imms token spender value ptr))
  exact ExecBlock.consRevert (allocateCallReverts cursorName allocateFunction_lookup
    (forceApproveCursorSource evm imms token spender value ptr)
    (by simp [evalExpr?, pure, uint256Value]; decide) hbad)

theorem forceApproveRevertsProbe (evm : State) (imms : Store) (token spender : AccountAddress)
    (value ptr : UInt256) (hfit : allocationFits ptr ⟨100⟩)
    (hprobe : ExecFuncBody config
      (optionalCallFrame imms token (constructorApproveCalldata spender value) (nextCursor ptr ⟨100⟩))
      evm allocatedOptionalReturnBoolFunction.body .reverted) :
    ExecFuncBody config (forceApproveFrame imms token spender value ptr) evm
      allocatedForceApproveFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply forceApproveAllocatePrefix evm imms token spender value ptr hfit
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := allocatedOptionalReturnBoolFunction)
    (forceApproveProbeArgs evm imms token spender value ptr) rfl rfl hprobe)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
