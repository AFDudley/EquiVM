import Benchmarks.Morpho.MetaMorphoV1_1.ERC4626DepositSource
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoFunctionSource
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateLastAssetsSource
import Benchmarks.Morpho.MetaMorphoV1_1.Storage

/-! Deposit's final total-assets update reads the actual state after market supply. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def depositFinish : List Stmt :=
  [.internalCall "_updateLastTotalAssets"
     [.inRange (.uint ⟨256, by decide⟩)
       (.binary .add (.storage ⟨"lastTotalAssets", []⟩) (.var "assets"))] "__c2",
   .return [.var cursorName]]

def depositUpdatedFrame (frame : Frame) : Frame :=
  { frame with locals := frame.locals.insert "__c2" .unit }

theorem depositLastAssetsSource {frame : Frame} {evm : State}
    (hc : frame.contract = contract) (hn : frame.locals.get? "lastTotalAssets" = none) :
    evalExpr? config frame evm (.storage ⟨"lastTotalAssets", []⟩) =
      .ok (uint256Value (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨22⟩)) := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hc hn
  subst c
  exact evalStorage_lastTotalAssets evm locals imms hn

theorem depositFinishSource {frame : Frame} {evm : State} {assets ptr : UInt256}
    (hc : frame.contract = contract) (hn : frame.locals.get? "lastTotalAssets" = none)
    (ha : frame.locals.get? "assets" = some (uint256Value assets))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hfit : (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨22⟩).toNat + assets.toNat < UInt256.size) :
    ExecBlock config frame evm depositFinish
      (.returned (depositUpdatedFrame frame)
        (updateLastAssetsState evm (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨22⟩ + assets))
        (some [uint256Value ptr])) := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hc hn ha hp
  subst c
  apply ExecBlock.consNormal (updateLastAssetsCall evm locals imms _ _ "__c2"
    (checkedAddSourceOk (depositLastAssetsSource rfl hn)
      (by simp only [evalExpr?, ha, EvalResult.ofOption]) hfit))
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?,
    store_get_ne _ _ (by decide : ("__c2" == cursorName) = false), hp,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem depositFinishSourceReverts {frame : Frame} {evm : State} {assets : UInt256}
    (hc : frame.contract = contract) (hn : frame.locals.get? "lastTotalAssets" = none)
    (ha : frame.locals.get? "assets" = some (uint256Value assets))
    (hbad : UInt256.size ≤
      (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨22⟩).toNat + assets.toNat) :
    ExecBlock config frame evm depositFinish .reverted := by
  have he := checkedAddSourceOverflow (rhs := .var "assets") (b := assets)
    (depositLastAssetsSource hc hn)
    (by simp only [evalExpr?, ha, EvalResult.ofOption]) hbad
  exact ExecBlock.consRevert (ExecStmt.internalCallArgsRevert
    (by simp only [evalExprs?, he, bind, EvalResult.bind]))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
