import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositArithmeticSource
import Benchmarks.Morpho.MetaMorphoV1_1.MinimumSource
import Benchmarks.Morpho.MetaMorphoV1_1.MarketBalancesSource

/-! Source arithmetic for one supply attempt. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def supplyMorphoAmount (shares sa ss cap assets : UInt256) : UInt256 :=
  minimumWord assets (maxDepositGap shares sa ss cap)

def supplyMorphoAssetsFrame (frame : Frame) (shares sa ss : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "supplyAssets" (uint256Value (assetsUpWord shares sa ss)) }

def supplyMorphoGapFrame (frame : Frame) (shares sa ss cap : UInt256) : Frame :=
  { supplyMorphoAssetsFrame frame shares sa ss with locals :=
      (supplyMorphoAssetsFrame frame shares sa ss).locals.insert "__c5" (uint256Value
        (maxDepositGap shares sa ss cap)) }

def supplyMorphoArithmeticFrame (frame : Frame) (shares sa ss cap assets : UInt256) : Frame :=
  { supplyMorphoGapFrame frame shares sa ss cap with locals :=
      (supplyMorphoGapFrame frame shares sa ss cap).locals.insert "toSupply" (uint256Value
        (supplyMorphoAmount shares sa ss cap assets)) }

theorem supplyMorphoAmount_le (shares sa ss cap assets : UInt256) :
    (supplyMorphoAmount shares sa ss cap assets).toNat ≤ assets.toNat := by
  rw [supplyMorphoAmount, minimumWord_toNat]
  exact Nat.min_le_left _ _

theorem supplyMorphoArithmeticFrame_preserves (frame : Frame) (shares sa ss cap assets : UInt256)
    (name : Ident) (ha : ("supplyAssets" == name) = false)
    (hg : ("__c5" == name) = false) (ht : ("toSupply" == name) = false) :
    (supplyMorphoArithmeticFrame frame shares sa ss cap assets).locals.get? name =
      frame.locals.get? name := by
  simp only [supplyMorphoArithmeticFrame, supplyMorphoGapFrame, supplyMorphoAssetsFrame,
    store_get_ne _ _ ha, store_get_ne _ _ hg, store_get_ne _ _ ht]

theorem supplyMorphoArithmeticFrame_amount (frame : Frame) (shares sa ss cap assets : UInt256) :
    (supplyMorphoArithmeticFrame frame shares sa ss cap assets).locals.get? "toSupply" =
      some (uint256Value (supplyMorphoAmount shares sa ss cap assets)) := store_get_self _ _ _

theorem supplyMorphoConversionSource {frame : Frame} {evm : State} {shares : UInt256}
    {market : ByteArray} (hcontract : frame.contract = contract)
    (hshares : frame.locals.get? "supplyShares" = some (uint256Value shares))
    (hmarket : frame.locals.get? "market" = some (marketValue market))
    (hfit : assetsUpFits shares (calldataWord market 0) (calldataWord market 32)) :
    ExecStmt config frame evm supplyMorphoArithmetic[0]!
      (.ok (supplyMorphoAssetsFrame frame shares (calldataWord market 0) (calldataWord market 32)) evm) := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hcontract hshares hmarket
  subst c
  apply assetsUpCall _ _ _ shares _ _ _ _ _ _ hfit
  · simp only [evalExpr?, hshares, EvalResult.ofOption]
  · exact marketFieldSource hmarket rfl
  · exact marketFieldSource hmarket rfl

theorem supplyMorphoConversionReverts {frame : Frame} {evm : State} {shares : UInt256}
    {market : ByteArray} (hcontract : frame.contract = contract)
    (hshares : frame.locals.get? "supplyShares" = some (uint256Value shares))
    (hmarket : frame.locals.get? "market" = some (marketValue market))
    (hbad : ¬ assetsUpFits shares (calldataWord market 0) (calldataWord market 32)) :
    ExecStmt config frame evm supplyMorphoArithmetic[0]! .reverted := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hcontract hshares hmarket
  subst c
  apply assetsUpCallReverts _ _ _ shares _ _ _ _ _ _ hbad
  · simp only [evalExpr?, hshares, EvalResult.ofOption]
  · exact marketFieldSource hmarket rfl
  · exact marketFieldSource hmarket rfl

theorem supplyMorphoGapSource {frame : Frame} {evm : State} {shares sa ss cap : UInt256}
    (hcontract : frame.contract = contract)
    (hcap : frame.locals.get? "supplyCap" = some (uint256Value cap)) :
    ExecStmt config (supplyMorphoAssetsFrame frame shares sa ss) evm supplyMorphoArithmetic[1]!
      (.ok (supplyMorphoGapFrame frame shares sa ss cap) evm) := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hcontract hcap
  subst c
  have he : uint256Value (maxDepositGap shares sa ss cap) =
      .int (Int.ofNat (cap.toNat - (assetsUpWord shares sa ss).toNat)) := by
    rw [uint256Value, maxDepositGap_toNat]
  simp only [supplyMorphoGapFrame, he]
  apply zeroFloorSubCall
  · simp only [evalExpr?, supplyMorphoAssetsFrame,
      store_get_ne _ _ (by decide : ("supplyAssets" == "supplyCap") = false),
      hcap, EvalResult.ofOption, uint256Value]
  · simp only [evalExpr?, supplyMorphoAssetsFrame, store_get_self, EvalResult.ofOption, uint256Value]

theorem supplyMorphoMinimumSource {frame : Frame} {evm : State} {shares sa ss cap assets : UInt256}
    (hcontract : frame.contract = contract)
    (hassets : frame.locals.get? "assets" = some (uint256Value assets)) :
    ExecStmt config (supplyMorphoGapFrame frame shares sa ss cap) evm supplyMorphoArithmetic[2]!
      (.ok (supplyMorphoArithmeticFrame frame shares sa ss cap assets) evm) := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hcontract hassets
  subst c
  unfold supplyMorphoArithmeticFrame supplyMorphoAmount
  rw [minimumWord_comm assets]
  apply minimumCall
  · simp only [evalExpr?, supplyMorphoGapFrame, store_get_self, EvalResult.ofOption]
  · simp only [evalExpr?, supplyMorphoGapFrame, supplyMorphoAssetsFrame,
      store_get_ne _ _ (by decide : ("__c5" == "assets") = false),
      store_get_ne _ _ (by decide : ("supplyAssets" == "assets") = false),
      hassets, EvalResult.ofOption]

theorem supplyMorphoArithmeticSource {frame : Frame} {evm : State} {shares cap assets : UInt256}
    {market : ByteArray} (hcontract : frame.contract = contract)
    (hshares : frame.locals.get? "supplyShares" = some (uint256Value shares))
    (hmarket : frame.locals.get? "market" = some (marketValue market))
    (hcap : frame.locals.get? "supplyCap" = some (uint256Value cap))
    (hassets : frame.locals.get? "assets" = some (uint256Value assets))
    (hfit : assetsUpFits shares (calldataWord market 0) (calldataWord market 32)) :
    ExecBlock config frame evm supplyMorphoArithmetic
      (.ok (supplyMorphoArithmeticFrame frame shares (calldataWord market 0)
        (calldataWord market 32) cap assets) evm) :=
  ExecBlock.consNormal (supplyMorphoConversionSource hcontract hshares hmarket hfit)
    (ExecBlock.consNormal (supplyMorphoGapSource hcontract hcap)
      (ExecBlock.consNormal (supplyMorphoMinimumSource hcontract hassets) ExecBlock.nil))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
