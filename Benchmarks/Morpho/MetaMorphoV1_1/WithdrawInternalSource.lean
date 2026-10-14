import Benchmarks.Morpho.MetaMorphoV1_1.ERC4626WithdrawSource
import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawMorphoFunctionSource
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateLastAssetsSource
import Benchmarks.Morpho.MetaMorphoV1_1.MarketArithmetic

/-! Source accounting and internal-call arguments for a vault withdrawal. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def withdrawAccounting : List Stmt :=
  [.internalCall "UtilsLib_zeroFloorSub" [.storage ⟨"lastTotalAssets", []⟩, .var "assets"] "__c0",
   .internalCall "_updateLastTotalAssets" [.var "__c0"] "__c1"]

def withdrawMarketStatements : List Stmt :=
  cursorCall allocatedWithdrawMorphoFunction.name [.var "assets"] "__c2"

def withdrawVaultStatement : Stmt :=
  .internalCall allocatedERC4626WithdrawFunction.name
    [.var "caller", .var "receiver", .var "owner", .var "assets", .var "shares", .var cursorName] cursorName

set_option maxRecDepth 2000 in
theorem allocatedWithdrawFunction_body :
    allocatedWithdrawFunction.body = withdrawAccounting ++ withdrawMarketStatements ++
      [withdrawVaultStatement, .return [.var cursorName]] := by decide +kernel

set_option maxRecDepth 2000 in
theorem allocatedWithdrawFunction_lookup :
    lookupCallable? contract allocatedWithdrawFunction.name = some allocatedWithdrawFunction.toCallable := by rfl

def withdrawAccountingFrame (frame : Frame) (remaining : UInt256) : Frame :=
  { frame with locals := (frame.locals.insert "__c0" (uint256Value remaining)).insert "__c1" .unit }

def withdrawRemainingAssets (evm : State) (assets : UInt256) : UInt256 :=
  UInt256.ofNat ((Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨22⟩).toNat - assets.toNat)

theorem withdrawRemainingAssets_toNat (evm : State) (assets : UInt256) :
    (withdrawRemainingAssets evm assets).toNat =
      (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨22⟩).toNat - assets.toNat := by
  apply UInt256.toNat_ofNat_of_lt
  exact lt_of_le_of_lt (Nat.sub_le _ _) (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨22⟩).val.isLt

theorem withdrawAccountingSource {frame : Frame} {evm : State} {assets : UInt256}
    (hc : frame.contract = contract) (hn : frame.locals.get? "lastTotalAssets" = none)
    (ha : frame.locals.get? "assets" = some (uint256Value assets)) :
    ExecBlock config frame evm withdrawAccounting
      (.ok (withdrawAccountingFrame frame (withdrawRemainingAssets evm assets))
        (updateLastAssetsState evm (withdrawRemainingAssets evm assets))) := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hc hn ha
  subst c
  have hv : uint256Value (withdrawRemainingAssets evm assets) = .int (Int.ofNat
      ((Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨22⟩).toNat - assets.toNat)) := by
    rw [uint256Value, withdrawRemainingAssets_toNat]
  have hzero := zeroFloorSubCall evm locals imms
    (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨22⟩).toNat assets.toNat "__c0"
    (.storage ⟨"lastTotalAssets", []⟩) (.var "assets")
    (evalStorage_lastTotalAssets evm locals imms hn)
    (by simp only [evalExpr?, ha, EvalResult.ofOption, uint256Value])
  rw [← hv] at hzero
  apply ExecBlock.consNormal hzero
  exact ExecBlock.consNormal (updateLastAssetsCall evm _ imms (withdrawRemainingAssets evm assets)
    (.var "__c0") "__c1" (by simp only [evalExpr?, store_get_self, EvalResult.ofOption])) ExecBlock.nil

theorem WithdrawVaultLocals.accounting {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {caller receiver owner : AccountAddress} {assets shares cursor : UInt256}
    (h : WithdrawVaultLocals v frame caller receiver owner assets shares cursor) (remaining : UInt256) :
    WithdrawVaultLocals v (withdrawAccountingFrame frame remaining) caller receiver owner assets shares cursor :=
  (h.insert "__c0" _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).insert
    "__c1" _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem WithdrawVaultLocals.market {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {caller receiver owner : AccountAddress} {assets shares cursor : UInt256}
    (h : WithdrawVaultLocals v frame caller receiver owner assets shares cursor) (ptr : UInt256) :
    WithdrawVaultLocals v (cursorResultFrame frame "__c2" (.tuple []) ptr)
      caller receiver owner assets shares ptr :=
  ((h.insert slotsAndCursorName _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).insert
    "__c2" _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).withCursor ptr

theorem withdrawMarketArgs {v : MetaMorphoV1_1Immutables} {frame : Frame} {evm : State}
    {caller receiver owner : AccountAddress} {assets shares cursor : UInt256}
    (h : WithdrawVaultLocals v frame caller receiver owner assets shares cursor) :
    evalExprs? config frame evm [.var "assets", .var cursorName] =
      .ok [uint256Value assets, uint256Value cursor] := by
  simp only [evalExprs?, evalExpr?, h.assets, h.cursor, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem withdrawVaultArgs {v : MetaMorphoV1_1Immutables} {frame : Frame} {evm : State}
    {caller receiver owner : AccountAddress} {assets shares cursor : UInt256}
    (h : WithdrawVaultLocals v frame caller receiver owner assets shares cursor) :
    evalExprs? config frame evm
      [.var "caller", .var "receiver", .var "owner", .var "assets", .var "shares", .var cursorName] =
      .ok [.address caller, .address receiver, .address owner, uint256Value assets,
        uint256Value shares, uint256Value cursor] := by
  simp only [evalExprs?, evalExpr?, h.caller, h.receiver, h.owner, h.assets, h.shares, h.cursor,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
