import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawMorphoLoopState

/-! Entry and return plumbing for the allocated market-withdrawal helper. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def allocatedWithdrawMorphoFrame (imms : Store) (assets ptr : UInt256) : Frame :=
  { contract := contract
    locals := ((∅ : Store).insert cursorName (uint256Value ptr)).insert "assets" (uint256Value assets)
    immutables := imms }

def withdrawMorphoTargetFrame (v : MetaMorphoV1_1Immutables) (assets ptr : UInt256) : Frame :=
  { allocatedWithdrawMorphoFrame (immStore v) assets ptr with locals :=
      (allocatedWithdrawMorphoFrame (immStore v) assets ptr).locals.insert "morphoTarget" (.address v.MORPHO) }

def withdrawMorphoInitialFrame (v : MetaMorphoV1_1Immutables) (assets ptr : UInt256) : Frame :=
  { withdrawMorphoTargetFrame v assets ptr with locals :=
      (withdrawMorphoTargetFrame v assets ptr).locals.insert "i" (uint256Value ⟨0⟩) }

theorem withdrawMorphoInitialLocals (v : MetaMorphoV1_1Immutables) (assets ptr : UInt256) :
    WithdrawMorphoLocals v (withdrawMorphoInitialFrame v assets ptr) ⟨0⟩ assets ptr := by
  constructor
  · constructor <;> simp [withdrawMorphoInitialFrame, withdrawMorphoTargetFrame,
      allocatedWithdrawMorphoFrame, cursorName, Std.HashMap.getElem_insert]
  · simp [withdrawMorphoInitialFrame, withdrawMorphoTargetFrame,
      allocatedWithdrawMorphoFrame, cursorName, Std.HashMap.getElem_insert]

set_option maxRecDepth 2000 in
theorem allocatedWithdrawMorphoFunction_lookup :
    lookupCallable? contract allocatedWithdrawMorphoFunction.name =
      some allocatedWithdrawMorphoFunction.toCallable := by rfl

theorem withdrawMorphoFunctionPrefix (v : MetaMorphoV1_1Immutables) (evm : State)
    (assets ptr : UInt256) :
    ABlock config evm (allocatedWithdrawMorphoFrame (immStore v) assets ptr)
      allocatedWithdrawMorphoFunction.body (withdrawMorphoTargetFrame v assets ptr)
      (allocatedWithdrawMorphoFunction.body.drop 1) := by
  constructor
  intro result htail
  rw [allocatedWithdrawMorphoFunction_body] at htail ⊢
  exact ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_MORPHO _ _ _ _ _)) htail

theorem withdrawMorphoForSource {v : MetaMorphoV1_1Immutables} {evm : State}
    {assets ptr : UInt256} {result : ExecResult}
    (hloop : ExecForLoop config (withdrawMorphoInitialFrame v assets ptr) evm
      accruedAssetsCondition accruedAssetsPost withdrawMorphoIteration result) :
    ExecStmt config (withdrawMorphoTargetFrame v assets ptr) evm
      (.for [.letDecl "i" (some abiUInt256) (.intLit 0)] accruedAssetsCondition accruedAssetsPost
        withdrawMorphoIteration) result := by
  apply ExecStmt.for ?_ hloop
  exact ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
    (by simp only [evalExpr?, pure]; rfl)) ExecBlock.nil

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
