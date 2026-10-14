import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateRowABI
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsHashSource
import Benchmarks.Morpho.MetaMorphoV1_1.MarketRemovalStorage
import Benchmarks.EAS.Attester.LocalArray

/-! Deferred row validation and construction of the source market allocation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
attribute [local irreducible] contract

def reallocateTupleFrame (frame : Frame) (value : Value) : Frame :=
  { frame with locals := frame.locals.insert "allocationTuple" value }

def reallocateParamsTupleFrame (frame : Frame) (row : ByteArray) : Frame :=
  { frame with locals := ((reallocateTupleFrame frame (reallocateRowValue row)).locals.insert
      "paramsTuple" (.tuple (marketParamsFields row))) }

def reallocateParamsFrame (frame : Frame) (row : ByteArray) : Frame :=
  { frame with locals := ((reallocateParamsTupleFrame frame row).locals.insert
      "params" (marketParamsData row).value) }

def reallocateAllocationValue (row : ByteArray) : Value :=
  .struct "MarketAllocation"
    [("marketParams", (marketParamsData row).value), ("assets", uint256Value (calldataWord row 160))]

def reallocateRowFrame (frame : Frame) (row : ByteArray) : Frame :=
  { frame with locals := ((reallocateParamsFrame frame row).locals.insert
      "allocation" (reallocateAllocationValue row)) }

def reallocateIdentifiedFrame (frame : Frame) (row : ByteArray) : Frame :=
  { frame with locals := ((reallocateRowFrame frame row).locals.insert
      "id" (wordBytes32Value (marketParamsData row).id)) }

theorem reallocateIdentifiedFrame_contract (frame : Frame) (row : ByteArray) :
    (reallocateIdentifiedFrame frame row).contract = frame.contract := by
  simp only [reallocateIdentifiedFrame]

theorem reallocateRowGuard_false (frame : Frame) (evm : State) :
    evalExpr? config (reallocateTupleFrame frame decodeFailure) evm
      (.binary .ne (.var "allocationTuple") (.structLit decodeFailureTag [])) =
      .ok (.bool false) := by
  simp only [evalExpr?, reallocateTupleFrame, store_get_self, EvalResult.ofOption,
    evalStructFields?, bind, EvalResult.bind, pure, evalBinaryOp?, decodeFailure]
  rfl

theorem reallocateRowGuard_true (frame : Frame) (evm : State) (row : ByteArray) :
    evalExpr? config (reallocateTupleFrame frame (reallocateRowValue row)) evm
      (.binary .ne (.var "allocationTuple") (.structLit decodeFailureTag [])) =
      .ok (.bool true) := by
  simp only [evalExpr?, reallocateTupleFrame, store_get_self, EvalResult.ofOption,
    evalStructFields?, bind, EvalResult.bind, pure, evalBinaryOp?]
  rfl

theorem reallocateRowDeclarationRevert {frame : Frame} {evm : State}
    {values : List Value} {i : Nat}
    (ha : frame.locals.get? "allocations" = some (.array values))
    (hi : frame.locals.get? "i" = some (.int (Int.ofNat i)))
    (hv : values[i]? = some decodeFailure) :
    ExecBlock config frame evm reallocateRowDeclarations .reverted := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalLocalArrayIndex ha hi hv rfl)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (reallocateRowGuard_false frame evm))

set_option maxRecDepth 2000 in
theorem reallocateRowDeclarationSource {frame : Frame} {evm : State}
    {values : List Value} {i : Nat} {row : ByteArray}
    (ha : frame.locals.get? "allocations" = some (.array values))
    (hi : frame.locals.get? "i" = some (.int (Int.ofNat i)))
    (hv : values[i]? = some (reallocateRowValue row)) :
    ExecBlock config frame evm reallocateRowDeclarations (.ok (reallocateRowFrame frame row) evm) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (evalLocalArrayIndex ha hi hv rfl)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (reallocateRowGuard_true frame evm row)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .tuple (marketParamsFields row)) ?_) ?_
  · simp only [evalExpr?, store_get_self, EvalResult.ofOption, reallocateRowValue,
      bind, EvalResult.bind, tupleGetValue?, List.getElem?_cons_zero]
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := (marketParamsData row).value) ?_) ?_
  · simp only [evalExpr?, evalStructFields?, store_get_self, EvalResult.ofOption,
      tupleGetValue?, marketParamsFields, List.getElem?_cons_zero, List.getElem?_cons_succ,
      bind, EvalResult.bind, pure, marketParamsData, MarketParamsData.value]
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := reallocateAllocationValue row) ?_) ExecBlock.nil
  simp only [evalExpr?, evalStructFields?, store_get_self,
    store_get_ne _ _ (by decide : ("params" == "allocationTuple") = false),
    store_get_ne _ _ (by decide : ("paramsTuple" == "allocationTuple") = false),
    EvalResult.ofOption, reallocateRowValue, tupleGetValue?,
    List.getElem?_cons_zero, List.getElem?_cons_succ, bind, EvalResult.bind, pure,
    reallocateAllocationValue]

theorem reallocateRowFrame_preserves (frame : Frame) (row : ByteArray) (name : Ident)
    (ha : ("allocation" == name) = false) (hp : ("params" == name) = false)
    (hpt : ("paramsTuple" == name) = false) (hat : ("allocationTuple" == name) = false) :
    (reallocateRowFrame frame row).locals.get? name = frame.locals.get? name := by
  simp only [reallocateRowFrame, reallocateParamsFrame, reallocateParamsTupleFrame,
    reallocateTupleFrame, store_get_ne _ _ ha, store_get_ne _ _ hp,
    store_get_ne _ _ hpt, store_get_ne _ _ hat]

theorem reallocateAllocationParams {frame : Frame} {evm : State} {row : ByteArray}
    (h : frame.locals.get? "allocation" = some (reallocateAllocationValue row)) :
    evalExpr? config frame evm (.field (.var "allocation") "marketParams") =
      .ok (marketParamsData row).value :=
  evalExpr_structField (evalLocalValue h) rfl

theorem reallocateAllocationAssets {frame : Frame} {evm : State} {row : ByteArray}
    (h : frame.locals.get? "allocation" = some (reallocateAllocationValue row)) :
    evalExpr? config frame evm (.field (.var "allocation") "assets") =
      .ok (uint256Value (calldataWord row 160)) :=
  evalExpr_structField (evalLocalValue h) rfl

theorem reallocateRowIdentifySource {frame : Frame} {evm : State} {row : ByteArray}
    (hc : frame.contract = contract) (hb : frame.locals.get? "config" = none)
    (henabled : marketRemovalEnabledWord evm (marketParamsData row).id ≠ ⟨0⟩) :
    ExecBlock config (reallocateRowFrame frame row) evm reallocateRowIdentify
      (.ok (reallocateIdentifiedFrame frame row) evm) := by
  have hcall := marketParamsIdCall evm (reallocateRowFrame frame row).locals frame.immutables
    (marketParamsData row) "id" (.field (.var "allocation") "marketParams")
    (reallocateAllocationParams (store_get_self _ _ _))
  have hcall' : ExecStmt config (reallocateRowFrame frame row) evm
      (.internalCall "MarketParamsLib_id" [.field (.var "allocation") "marketParams"] "id")
      (.ok (reallocateIdentifiedFrame frame row) evm) := by
    simpa only [reallocateIdentifiedFrame, reallocateRowFrame, reallocateParamsFrame,
      reallocateParamsTupleFrame, reallocateTupleFrame, hc] using hcall
  refine ExecBlock.consNormal hcall' (ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil)
  have hread := marketRemovalEnabledRead (frame := reallocateIdentifiedFrame frame row) (evm := evm)
      (id := (marketParamsData row).id) (by rw [reallocateIdentifiedFrame_contract]; exact hc)
    (by rw [reallocateIdentifiedFrame, store_get_ne _ _ (by decide),
        reallocateRowFrame_preserves _ _ _ (by decide) (by decide) (by decide) (by decide)]; exact hb)
    (store_get_self _ _ _)
  rw [decide_eq_true henabled] at hread
  exact hread

theorem reallocateRowIdentifyRevert {frame : Frame} {evm : State} {row : ByteArray}
    (hc : frame.contract = contract) (hb : frame.locals.get? "config" = none)
    (hdisabled : marketRemovalEnabledWord evm (marketParamsData row).id = ⟨0⟩) :
    ExecBlock config (reallocateRowFrame frame row) evm reallocateRowIdentify .reverted := by
  have hcall := marketParamsIdCall evm (reallocateRowFrame frame row).locals frame.immutables
    (marketParamsData row) "id" (.field (.var "allocation") "marketParams")
    (reallocateAllocationParams (store_get_self _ _ _))
  have hcall' : ExecStmt config (reallocateRowFrame frame row) evm
      (.internalCall "MarketParamsLib_id" [.field (.var "allocation") "marketParams"] "id")
      (.ok (reallocateIdentifiedFrame frame row) evm) := by
    simpa only [reallocateIdentifiedFrame, reallocateRowFrame, reallocateParamsFrame,
      reallocateParamsTupleFrame, reallocateTupleFrame, hc] using hcall
  refine ExecBlock.consNormal hcall' (ExecBlock.consRevert (ExecStmt.requireFalse ?_))
  have hread := marketRemovalEnabledRead (frame := reallocateIdentifiedFrame frame row) (evm := evm)
      (id := (marketParamsData row).id) (by rw [reallocateIdentifiedFrame_contract]; exact hc)
      (by rw [reallocateIdentifiedFrame, store_get_ne _ _ (by decide),
          reallocateRowFrame_preserves _ _ _ (by decide) (by decide) (by decide) (by decide)]; exact hb)
      (store_get_self _ _ _)
  rw [hdisabled] at hread
  exact hread

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
