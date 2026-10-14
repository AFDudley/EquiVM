import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateArithmeticSource

/-! Source computation of the supply amount, including the zero-amount continue. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
attribute [local irreducible] contract

def reallocateSupplyAmount (target assets supplied withdrawn : UInt256) : UInt256 :=
  if target = UInt256.lnot ⟨0⟩ then UInt256.ofNat (withdrawn.toNat - supplied.toNat)
  else UInt256.ofNat (target.toNat - assets.toNat)

def reallocateSupplyAmountFrame (frame : Frame) (target assets supplied withdrawn : UInt256) : Frame :=
  { frame with locals := (((frame.locals.insert "__c7"
      (uint256Value (UInt256.ofNat (withdrawn.toNat - supplied.toNat)))).insert "__c8"
      (uint256Value (UInt256.ofNat (target.toNat - assets.toNat)))).insert "suppliedAssets"
      (uint256Value (reallocateSupplyAmount target assets supplied withdrawn))) }

set_option maxRecDepth 2000 in
theorem reallocateSupplyAmountSource {frame : Frame} {evm : State} {row : ByteArray}
    {assets supplied withdrawn : UInt256} (hc : frame.contract = contract)
    (hts : frame.locals.get? "totalSupplied" = some (uint256Value supplied))
    (htw : frame.locals.get? "totalWithdrawn" = some (uint256Value withdrawn))
    (ha : frame.locals.get? "supplyAssets" = some (uint256Value assets))
    (hr : frame.locals.get? "allocation" = some (reallocateAllocationValue row)) :
    ExecBlock config frame evm (reallocateSupplyBody.take 3)
      (.ok (reallocateSupplyAmountFrame frame (calldataWord row 160) assets supplied withdrawn) evm) := by
  apply ExecBlock.consNormal (zeroFloorSubCallFrame "__c7" hc (evalLocalValue htw) (evalLocalValue hts))
  let frame1 : Frame := { frame with locals := (frame.locals.insert "__c7"
    (uint256Value (UInt256.ofNat (withdrawn.toNat - supplied.toNat)))) }
  have hr1 : frame1.locals.get? "allocation" = some (reallocateAllocationValue row) := by
    rw [store_get_ne _ _ (by decide)]; exact hr
  have ha1 : frame1.locals.get? "supplyAssets" = some (uint256Value assets) := by
    rw [store_get_ne _ _ (by decide)]; exact ha
  apply ExecBlock.consNormal (zeroFloorSubCallFrame (frame := frame1) "__c8" hc
    (reallocateAllocationAssets hr1) (evalLocalValue ha1))
  let frame2 : Frame := { frame1 with locals := (frame1.locals.insert "__c8"
    (uint256Value (UInt256.ofNat ((calldataWord row 160).toNat - assets.toNat)))) }
  have hr2 : frame2.locals.get? "allocation" = some (reallocateAllocationValue row) := by
    rw [store_get_ne _ _ (by decide)]; exact hr1
  have htest := wordEqSource (evm := evm) (reallocateAllocationAssets hr2)
    (show evalExpr? config frame2 evm (.intLit (Int.ofNat (2 ^ 256 - 1))) =
      .ok (uint256Value (UInt256.lnot ⟨0⟩)) by
      simp only [evalExpr?, pure, uint256Value, u256_lnot_zero_toNat]; rfl)
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value
    (reallocateSupplyAmount (calldataWord row 160) assets supplied withdrawn)) ?_) ExecBlock.nil
  change evalExpr? config frame2 evm (.ite _ _ _) = _
  rw [evalExpr?, htest]
  simp only [bind, EvalResult.bind, reallocateSupplyAmount,
    evalExpr?,
    frame2, frame1, store_get_self,
    store_get_ne _ _ (by decide : ("__c8" == "__c7") = false), EvalResult.ofOption]
  by_cases ht : calldataWord row 160 = UInt256.lnot ⟨0⟩ <;> simp only [ht, decide_true,
    decide_false, if_true, if_false]

theorem reallocateSupplyAmountFrame_preserves (frame : Frame) (target assets supplied withdrawn : UInt256)
    (name : Ident) (h7 : ("__c7" == name) = false) (h8 : ("__c8" == name) = false)
    (ha : ("suppliedAssets" == name) = false) :
    (reallocateSupplyAmountFrame frame target assets supplied withdrawn).locals.get? name =
      frame.locals.get? name := by
  rw [reallocateSupplyAmountFrame, store_get_ne _ _ ha, store_get_ne _ _ h8, store_get_ne _ _ h7]

theorem ReallocateLocals.supplyAmount {v : MetaMorphoV1_1Immutables} {frame : Frame} {values : List Value}
    {i supplied withdrawn cursor : UInt256} (h : ReallocateLocals v frame values i supplied withdrawn cursor)
    (target assets : UInt256) :
    ReallocateLocals v (reallocateSupplyAmountFrame frame target assets supplied withdrawn)
      values i supplied withdrawn cursor :=
  ((h.insert "__c7" _ (by decide)).insert "__c8" _ (by decide)).insert "suppliedAssets" _ (by decide)

theorem reallocateSupplyContinueSource {frame : Frame} {evm : State} {amount : UInt256}
    (ha : frame.locals.get? "suppliedAssets" = some (uint256Value amount)) (hz : amount = ⟨0⟩) :
    ExecBlock config frame evm (reallocateSupplyBody.drop 3) (.continue frame evm) := by
  have ht := wordEqSource (evm := evm) (evalLocalValue ha)
    (show evalExpr? config frame evm (.intLit 0) = .ok (uint256Value ⟨0⟩) by simp only [evalExpr?, pure]; rfl)
  rw [decide_eq_true hz] at ht
  exact ExecBlock.consContinue (ExecStmt.iteTrue ht (ExecBlock.consContinue ExecStmt.continue))

theorem reallocateSupplyNonzeroSource {frame : Frame} {evm : State} {amount : UInt256}
    (ha : frame.locals.get? "suppliedAssets" = some (uint256Value amount)) (hz : amount ≠ ⟨0⟩) :
    ABlock config evm frame (reallocateSupplyBody.drop 3) frame (reallocateSupplyBody.drop 4) := by
  have ht := wordEqSource (evm := evm) (evalLocalValue ha)
    (show evalExpr? config frame evm (.intLit 0) = .ok (uint256Value ⟨0⟩) by simp only [evalExpr?, pure]; rfl)
  rw [decide_eq_false hz] at ht
  exact ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.iteFalse ht ExecBlock.nil) h⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
