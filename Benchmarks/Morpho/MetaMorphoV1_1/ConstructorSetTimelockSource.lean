import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorTimelockInit
import Benchmarks.Morpho.MetaMorphoV1_1.SetTimelockSource

/-! Source continuation through the initial timelock assignment and event. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def constructorSetTimelockFrame (frame : Frame) : Frame :=
  { frame with locals := frame.locals.insert "initTime" .unit }

def constructorTimelockReadyFrame (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (I : ExecutionEnv) : Frame :=
  constructorSetTimelockFrame (constructorTimelockCheckedFrame
    (constructorOwnershipFrame (constructorDomainReadyFrame a ok out I)) a.initialTimelock)

theorem constructorSetTimelockSource {frame : Frame} {evm : State} {value : UInt256}
    (hcontract : frame.contract = contract)
    (hget : frame.locals.get? "initialTimelock" = some (uint256Value value)) :
    ExecStmt config frame evm (.internalCall "_setTimelock" [.var "initialTimelock"] "initTime")
      (.ok (constructorSetTimelockFrame frame) (setTimelockState evm value)) := by
  rcases frame with ⟨decl, locals, imms⟩
  change decl = contract at hcontract
  subst decl
  exact setTimelockCall evm locals imms value (.var "initialTimelock") "initTime"
    (by simp only [evalExpr?, hget, EvalResult.ofOption])

theorem constructorTimelockCheckedFrame_contract {frame : Frame} (value : UInt256)
    (hcontract : frame.contract = contract) :
    (constructorTimelockCheckedFrame frame value).contract = contract := by
  unfold constructorTimelockCheckedFrame
  split <;> exact hcontract

theorem constructorTimelockCheckedFrame_value {frame : Frame} {value : UInt256}
    (hget : frame.locals.get? "initialTimelock" = some (uint256Value value)) :
    (constructorTimelockCheckedFrame frame value).locals.get? "initialTimelock" =
      some (uint256Value value) := by
  unfold constructorTimelockCheckedFrame
  split
  · exact hget
  · rw [store_get_ne _ _ (by decide)]
    exact hget

theorem constructorSetTimelockBodySplit : contract.ctor.body.drop 28 =
    .internalCall "_setTimelock" [.var "initialTimelock"] "initTime" :: contract.ctor.body.drop 29 := rfl

theorem constructorSetTimelockPrefix {frame : Frame} {evm : State} {value : UInt256}
    {result : ExecResult} (hcontract : frame.contract = contract)
    (hget : frame.locals.get? "initialTimelock" = some (uint256Value value))
    (htail : ExecBlock config (constructorSetTimelockFrame frame) (setTimelockState evm value)
      (contract.ctor.body.drop 29) result) :
    ExecBlock config frame evm (contract.ctor.body.drop 28) result := by
  rw [constructorSetTimelockBodySplit]
  exact ExecBlock.consNormal (constructorSetTimelockSource hcontract hget) htail

end Benchmarks.Morpho.MetaMorphoV1_1
