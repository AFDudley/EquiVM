import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorTimelockGuard
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorOwnershipSource
import Benchmarks.Morpho.MetaMorphoV1_1.MarketBalancesSource

/-! Source execution of the constructor's optional timelock range check. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def constructorTimelockCondition : Expr := .binary .ne (.var "initialTimelock") (.intLit 0)

def constructorTimelockCheckStmt : Stmt :=
  .ite constructorTimelockCondition
    [.internalCall "_checkTimelockBounds" [.var "initialTimelock"] "checkTime"] []

def constructorTimelockCheckedFrame (frame : Frame) (value : UInt256) : Frame :=
  if value = ⟨0⟩ then frame else { frame with locals := frame.locals.insert "checkTime" .unit }

theorem constructorTimelockConditionSource {frame : Frame} {evm : State} {value : UInt256}
    (hget : frame.locals.get? "initialTimelock" = some (uint256Value value)) :
    evalExpr? config frame evm constructorTimelockCondition = .ok (.bool (decide (value ≠ ⟨0⟩))) := by
  exact wordNeSource (by simp only [evalExpr?, hget, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]; rfl)

theorem constructorTimelockCheckSource {frame : Frame} {evm : State} {value : UInt256}
    (hcontract : frame.contract = contract)
    (hget : frame.locals.get? "initialTimelock" = some (uint256Value value))
    (hgood : constructorTimelockValid value) :
    ExecStmt config frame evm constructorTimelockCheckStmt
      (.ok (constructorTimelockCheckedFrame frame value) evm) := by
  by_cases hz : value = ⟨0⟩
  · rw [constructorTimelockCheckedFrame, if_pos hz]
    exact ExecStmt.iteFalse (by
      simpa only [hz, ne_eq, not_true_eq_false, decide_false] using constructorTimelockConditionSource hget)
      ExecBlock.nil
  · have hb : timelockInBounds value := hgood.resolve_left hz
    rw [constructorTimelockCheckedFrame, if_neg hz]
    apply ExecStmt.iteTrue (by
      simpa only [ne_eq, hz, not_false_eq_true, decide_true] using constructorTimelockConditionSource hget)
    rcases frame with ⟨decl, locals, imms⟩
    change decl = contract at hcontract
    subst decl
    exact ExecBlock.consNormal (timelockBoundsCall evm locals imms value (.var "initialTimelock")
      "checkTime" hb (by simp only [evalExpr?, hget, EvalResult.ofOption])) ExecBlock.nil

theorem constructorTimelockCheckReverts {frame : Frame} {evm : State} {value : UInt256}
    (hcontract : frame.contract = contract)
    (hget : frame.locals.get? "initialTimelock" = some (uint256Value value))
    (hbad : ¬ constructorTimelockValid value) :
    ExecStmt config frame evm constructorTimelockCheckStmt .reverted := by
  have hz : value ≠ ⟨0⟩ := fun h ↦ hbad (.inl h)
  have hb : ¬ timelockInBounds value := fun h ↦ hbad (.inr h)
  apply ExecStmt.iteTrue (by
    simpa only [ne_eq, hz, not_false_eq_true, decide_true] using constructorTimelockConditionSource hget)
  rcases frame with ⟨decl, locals, imms⟩
  change decl = contract at hcontract
  subst decl
  exact ExecBlock.consRevert (timelockBoundsCallReverts evm locals imms value (.var "initialTimelock")
    "checkTime" hb (by simp only [evalExpr?, hget, EvalResult.ofOption]))

theorem constructorTimelockCheckBodySplit : contract.ctor.body.drop 27 =
    constructorTimelockCheckStmt :: contract.ctor.body.drop 28 := rfl

theorem constructorTimelockCheckPrefix {frame : Frame} {evm : State} {value : UInt256}
    {result : ExecResult} (hcontract : frame.contract = contract)
    (hget : frame.locals.get? "initialTimelock" = some (uint256Value value))
    (hgood : constructorTimelockValid value)
    (htail : ExecBlock config (constructorTimelockCheckedFrame frame value) evm
      (contract.ctor.body.drop 28) result) :
    ExecBlock config frame evm (contract.ctor.body.drop 27) result := by
  rw [constructorTimelockCheckBodySplit]
  exact ExecBlock.consNormal (constructorTimelockCheckSource hcontract hget hgood) htail

end Benchmarks.Morpho.MetaMorphoV1_1
