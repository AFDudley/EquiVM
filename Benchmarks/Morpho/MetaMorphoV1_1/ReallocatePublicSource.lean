import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateArithmeticSource
import Benchmarks.Morpho.MetaMorphoV1_1.AllocatorRoleSource
import Benchmarks.Morpho.MetaMorphoV1_1.BodyCommon

/-! Public reallocation initialization and the final conservation check. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000
attribute [local irreducible] contract

def reallocateEntryFrame (evm : State) (v : MetaMorphoV1_1Immutables)
    (values : List Value) : Frame :=
  ⟨contract, ((((∅ : Store).insert "allocations" (.array values)).insert
    "morphoTarget" (.address v.MORPHO)).insert "__calldata"
      (.bytes evm.executionEnv.calldata)).insert cursorName (uint256Value ⟨128⟩), immStore v⟩

def reallocatePublicFrame (evm : State) (v : MetaMorphoV1_1Immutables)
    (values : List Value) : Frame :=
  let frame := reallocateEntryFrame evm v values
  { frame with locals := (((frame.locals.insert "__role" .unit).insert
    "totalSupplied" (uint256Value ⟨0⟩)).insert "totalWithdrawn" (uint256Value ⟨0⟩)) }

def reallocateIndexFrame (frame : Frame) : Frame :=
  { frame with locals := frame.locals.insert "i" (uint256Value ⟨0⟩) }

def reallocateFinalCheck : Stmt :=
  .require (.binary .eq (.var "totalWithdrawn") (.var "totalSupplied"))

theorem reallocateEntrySource (evm : State) (v : MetaMorphoV1_1Immutables)
    (values : List Value) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm ⟨contract, (∅ : Store).insert "allocations" (.array values), immStore v⟩
      allocatedReallocateTransition.body (reallocateEntryFrame evm v values)
      [.internalCall "_checkAllocatorRole" [] "__role",
       .letDecl "totalSupplied" (some cursorType) (.intLit 0),
       .letDecl "totalWithdrawn" (some cursorType) (.intLit 0),
       reallocateLoop, reallocateFinalCheck] := by
  constructor
  intro result htail
  rw [allocatedReallocateTransition_body]
  apply ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv))
  apply ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_MORPHO config contract _ evm v))
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .bytes evm.executionEnv.calldata)
    (by simp only [evalExpr?, envValue, pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact (evalLocalBytesLengthLt (cfg := config) (evm := evm)
        (stele := ⟨contract, (((∅ : Store).insert "allocations" (.array values)).insert
          "morphoTarget" (.address v.MORPHO)).insert "__calldata"
            (.bytes evm.executionEnv.calldata), immStore v⟩)
        (2 ^ 255 + 4) (store_get_self _ _ _)).trans (by rw [decide_eq_true hhi])
  exact ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨128⟩)
    (by simp only [evalExpr?, pure]; rfl)) htail

theorem reallocateRoleRevertsSource (evm : State) (v : MetaMorphoV1_1Immutables)
    (values : List Value) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hrole : ¬ allocatorRoleAllowed evm) :
    ExecTransitionBody config contract evm ((∅ : Store).insert "allocations" (.array values))
      allocatedReallocateTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply (reallocateEntrySource evm v values hwv hhi).run
  exact ExecBlock.consRevert (allocatorRoleCallReverts evm _ (immStore v) "__role" hrole)

theorem reallocatePublicPrefix (evm : State) (v : MetaMorphoV1_1Immutables)
    (values : List Value) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hrole : allocatorRoleAllowed evm) :
    ABlock config evm ⟨contract, (∅ : Store).insert "allocations" (.array values), immStore v⟩
      allocatedReallocateTransition.body (reallocatePublicFrame evm v values)
      [reallocateLoop, reallocateFinalCheck] := by
  constructor
  intro result htail
  apply (reallocateEntrySource evm v values hwv hhi).run
  apply ExecBlock.consNormal (allocatorRoleCall evm _ (immStore v) "__role" hrole)
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
    (by simp only [evalExpr?, pure]; rfl))
  exact ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
    (by simp only [evalExpr?, pure]; rfl)) htail

theorem reallocateForInit (frame : Frame) (evm : State) :
    ExecBlock config frame evm [.letDecl "i" (some cursorType) (.intLit 0)]
      (.ok (reallocateIndexFrame frame) evm) :=
  ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
    (by simp only [evalExpr?, pure]; rfl)) ExecBlock.nil

theorem reallocateInitialLocals (evm : State) (v : MetaMorphoV1_1Immutables)
    (values : List Value) :
    ReallocateLocals v (reallocateIndexFrame (reallocatePublicFrame evm v values))
      values ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨128⟩ := by
  constructor <;> simp only [reallocateIndexFrame, reallocatePublicFrame, reallocateEntryFrame]
  all_goals repeat first | rw [store_get_self] | rw [store_get_ne _ _ (by decide)]
  simp

theorem reallocateFinalCheckSource {frame : Frame} {evm : State}
    {supplied withdrawn : UInt256}
    (hs : frame.locals.get? "totalSupplied" = some (uint256Value supplied))
    (hw : frame.locals.get? "totalWithdrawn" = some (uint256Value withdrawn)) :
    evalExpr? config frame evm (.binary .eq (.var "totalWithdrawn") (.var "totalSupplied")) =
      .ok (.bool (decide (withdrawn = supplied))) :=
  wordEqSource (evalLocalValue hw) (evalLocalValue hs)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
