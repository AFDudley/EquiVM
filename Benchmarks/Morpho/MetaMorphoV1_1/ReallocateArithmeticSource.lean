import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateBalancesSource
import Benchmarks.Morpho.MetaMorphoV1_1.MarketArithmetic

/-! The clamped amount calculation and full-withdrawal choice in reallocation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
attribute [local irreducible] contract

-- LIBRARY CANDIDATE: natural subtraction of word values fits a word without an additional bound.
theorem uint256Value_subNat (a b : UInt256) :
    uint256Value (UInt256.ofNat (a.toNat - b.toNat)) = .int (Int.ofNat (a.toNat - b.toNat)) := by
  have hf : a.toNat - b.toNat < UInt256.size := lt_of_le_of_lt (Nat.sub_le _ _) a.val.isLt
  rw [uint256Value, UInt256.toNat_ofNat_of_lt hf]

theorem zeroFloorSubCallFrame {frame : Frame} {evm : State} {a b : UInt256}
    {lhs rhs : Expr} (retVar : Ident) (hc : frame.contract = contract)
    (ha : evalExpr? config frame evm lhs = .ok (uint256Value a))
    (hb : evalExpr? config frame evm rhs = .ok (uint256Value b)) :
    ExecStmt config frame evm (.internalCall "UtilsLib_zeroFloorSub" [lhs, rhs] retVar)
      (.ok { frame with locals := (frame.locals.insert retVar
        (uint256Value (UInt256.ofNat (a.toNat - b.toNat)))) } evm) := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hc
  subst c
  rw [uint256Value_subNat]
  exact zeroFloorSubCall evm locals imms a.toNat b.toNat retVar lhs rhs ha hb

-- LIBRARY CANDIDATE: equality of evaluated uint256 expressions in an arbitrary source frame.
theorem wordEqSource {cfg : Config} {frame : Frame} {evm : State} {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg frame evm rhs = .ok (uint256Value b)) :
    evalExpr? cfg frame evm (.binary .eq lhs rhs) = .ok (.bool (decide (a = b))) := by
  have hinj : a.toNat = b.toNat ↔ a = b := ⟨u256_inj, fun h ↦ congrArg UInt256.toNat h⟩
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  simp [ha, hb, bind, EvalResult.bind, uint256Value, evalBinaryOp?, BEq.beq, hinj]

def reallocateAmountFrame (frame : Frame) (assets target : UInt256) : Frame :=
  { frame with locals := (frame.locals.insert "withdrawn"
    (uint256Value (UInt256.ofNat (assets.toNat - target.toNat)))) }

theorem reallocateAmountSource {frame : Frame} {evm : State} {row : ByteArray} {assets : UInt256}
    (hc : frame.contract = contract)
    (ha : frame.locals.get? "supplyAssets" = some (uint256Value assets))
    (hr : frame.locals.get? "allocation" = some (reallocateAllocationValue row)) :
    ExecStmt config frame evm reallocateRowAmount
      (.ok (reallocateAmountFrame frame assets (calldataWord row 160)) evm) :=
  zeroFloorSubCallFrame "withdrawn" hc (evalLocalValue ha) (reallocateAllocationAssets hr)

theorem ReallocateLocals.amount {v : MetaMorphoV1_1Immutables} {frame : Frame} {values : List Value}
    {i supplied withdrawn cursor : UInt256} (h : ReallocateLocals v frame values i supplied withdrawn cursor)
    (assets target : UInt256) :
    ReallocateLocals v (reallocateAmountFrame frame assets target) values i supplied withdrawn cursor :=
  h.insert "withdrawn" _ (by decide)

def reallocateWithdrawSetupFrame (frame : Frame) (target shares : UInt256) : Frame :=
  let locals := frame.locals.insert "shares" (uint256Value ⟨0⟩)
  { frame with locals := if target = ⟨0⟩ then
      (locals.insert "shares" (uint256Value shares)).insert "withdrawn" (uint256Value ⟨0⟩)
    else locals }

set_option maxRecDepth 2000 in
theorem reallocateWithdrawSetupSource {frame : Frame} {evm : State} {row : ByteArray} {shares amount : UInt256}
    (hr : frame.locals.get? "allocation" = some (reallocateAllocationValue row))
    (hs : frame.locals.get? "supplyShares" = some (uint256Value shares))
    (hw : frame.locals.get? "withdrawn" = some (uint256Value amount)) :
    ExecBlock config frame evm (reallocateWithdrawBody.take 2)
      (.ok (reallocateWithdrawSetupFrame frame (calldataWord row 160) shares) evm) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
    (by simp only [evalExpr?, pure]; rfl)) ?_
  let frame1 : Frame := { frame with locals := frame.locals.insert "shares" (uint256Value ⟨0⟩) }
  have hr1 : frame1.locals.get? "allocation" = some (reallocateAllocationValue row) := by
    rw [store_get_ne _ _ (by decide)]; exact hr
  have htest := wordEqSource (evm := evm) (reallocateAllocationAssets hr1)
    (show evalExpr? config frame1 evm (.intLit 0) = .ok (uint256Value ⟨0⟩) by
      simp only [evalExpr?, pure]; rfl)
  by_cases hz : calldataWord row 160 = ⟨0⟩
  · rw [decide_eq_true hz] at htest
    simp only [reallocateWithdrawSetupFrame, if_pos hz]
    apply ExecBlock.consNormal (ExecStmt.iteTrue htest ?_) ExecBlock.nil
    refine ExecBlock.consNormal (ExecStmt.assign (value := uint256Value shares) ?_
      (assignLocalValue (store_get_self _ _ _))) ?_
    · simp only [evalExpr?, frame1,
        store_get_ne _ _ (by decide : ("shares" == "supplyShares") = false), hs, EvalResult.ofOption]
    refine ExecBlock.consNormal (ExecStmt.assign (value := uint256Value ⟨0⟩) ?_
      (assignLocalValue (old := uint256Value amount) ?_)) ExecBlock.nil
    · simp only [evalExpr?, pure]; rfl
    · simp only [frame1,
        store_get_ne _ _ (by decide : ("shares" == "withdrawn") = false), hw]
  · rw [decide_eq_false hz] at htest
    simpa only [reallocateWithdrawSetupFrame, if_neg hz] using
      (ExecBlock.consNormal (ExecStmt.iteFalse htest ExecBlock.nil) (ExecBlock.nil (cfg := config)
        (stele := frame1) (evm := evm)))

theorem reallocateWithdrawSetupFrame_preserves (frame : Frame) (target shares : UInt256) (name : Ident)
    (hs : ("shares" == name) = false) (hw : ("withdrawn" == name) = false) :
    (reallocateWithdrawSetupFrame frame target shares).locals.get? name = frame.locals.get? name := by
  unfold reallocateWithdrawSetupFrame
  split <;> simp only [store_get_ne _ _ hs, store_get_ne _ _ hw]

theorem reallocateWithdrawSetupFrame_shares (frame : Frame) (target shares : UInt256) :
    (reallocateWithdrawSetupFrame frame target shares).locals.get? "shares" =
      some (uint256Value (if target = ⟨0⟩ then shares else ⟨0⟩)) := by
  unfold reallocateWithdrawSetupFrame
  split <;> simp only [store_get_self, store_get_ne _ _ (by decide : ("withdrawn" == "shares") = false)]

theorem reallocateWithdrawSetupFrame_amount {frame : Frame} (target shares amount : UInt256)
    (hw : frame.locals.get? "withdrawn" = some (uint256Value amount)) :
    (reallocateWithdrawSetupFrame frame target shares).locals.get? "withdrawn" =
      some (uint256Value (if target = ⟨0⟩ then ⟨0⟩ else amount)) := by
  unfold reallocateWithdrawSetupFrame
  split <;> simp only [store_get_self, store_get_ne _ _ (by decide : ("shares" == "withdrawn") = false), hw]

theorem ReallocateLocals.withdrawSetup {v : MetaMorphoV1_1Immutables} {frame : Frame} {values : List Value}
    {i supplied withdrawn cursor : UInt256} (h : ReallocateLocals v frame values i supplied withdrawn cursor)
    (target shares : UInt256) :
    ReallocateLocals v (reallocateWithdrawSetupFrame frame target shares) values i supplied withdrawn cursor := by
  unfold reallocateWithdrawSetupFrame
  split
  · exact ((h.insert "shares" (uint256Value ⟨0⟩) (by decide)).insert "shares"
      (uint256Value shares) (by decide)).insert "withdrawn" (uint256Value ⟨0⟩) (by decide)
  · exact h.insert "shares" (uint256Value ⟨0⟩) (by decide)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
