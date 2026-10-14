import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoLoopState

/-! Entry and return plumbing for the allocated market-supply helper. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def allocatedSupplyMorphoFrame (imms : Store) (assets ptr : UInt256) : Frame :=
  { contract := contract
    locals := ((∅ : Store).insert cursorName (uint256Value ptr)).insert "assets" (uint256Value assets)
    immutables := imms }

def supplyMorphoTargetFrame (v : MetaMorphoV1_1Immutables) (assets ptr : UInt256) : Frame :=
  { allocatedSupplyMorphoFrame (immStore v) assets ptr with locals :=
      (allocatedSupplyMorphoFrame (immStore v) assets ptr).locals.insert "morphoTarget" (.address v.MORPHO) }

def supplyMorphoInitialFrame (v : MetaMorphoV1_1Immutables) (assets ptr : UInt256) : Frame :=
  { supplyMorphoTargetFrame v assets ptr with locals :=
      (supplyMorphoTargetFrame v assets ptr).locals.insert "i" (uint256Value ⟨0⟩) }

theorem supplyMorphoInitialLocals (v : MetaMorphoV1_1Immutables) (assets ptr : UInt256) :
    SupplyLoopLocals v (supplyMorphoInitialFrame v assets ptr) ⟨0⟩ assets ptr := by
  constructor <;> simp [supplyMorphoInitialFrame, supplyMorphoTargetFrame,
    allocatedSupplyMorphoFrame, cursorName, Std.HashMap.getElem_insert]

set_option maxRecDepth 2000 in
theorem allocatedSupplyMorphoFunction_lookup :
    lookupCallable? contract allocatedSupplyMorphoFunction.name =
      some allocatedSupplyMorphoFunction.toCallable := by rfl

theorem supplyMorphoFunctionPrefix (v : MetaMorphoV1_1Immutables) (evm : State)
    (assets ptr : UInt256) :
    ABlock config evm (allocatedSupplyMorphoFrame (immStore v) assets ptr)
      allocatedSupplyMorphoFunction.body (supplyMorphoTargetFrame v assets ptr)
      (allocatedSupplyMorphoFunction.body.drop 1) := by
  constructor
  intro result htail
  rw [allocatedSupplyMorphoFunction_body] at htail ⊢
  exact ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_MORPHO _ _ _ _ _)) htail

theorem supplyMorphoForSource {v : MetaMorphoV1_1Immutables} {evm : State}
    {assets ptr : UInt256} {result : ExecResult}
    (hloop : ExecForLoop config (supplyMorphoInitialFrame v assets ptr) evm
      maxDepositCondition maxDepositPost supplyMorphoIteration result) :
    ExecStmt config (supplyMorphoTargetFrame v assets ptr) evm
      (.for [.letDecl "i" (some abiUInt256) (.intLit 0)] maxDepositCondition maxDepositPost
        supplyMorphoIteration) result := by
  apply ExecStmt.for ?_ hloop
  exact ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value ⟨0⟩)
    (by simp only [evalExpr?, pure]; rfl)) ExecBlock.nil

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
