import Benchmarks.Morpho.MetaMorphoV1_1.DepositFinishSource

/-! Source calls joining the ERC4626 deposit, Morpho supply, and final accounting. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def depositSupplyStatements : List Stmt :=
  cursorCall allocatedSupplyMorphoFunction.name [.var "assets"] "__c1"

def depositSuppliedFrame (imms : Store) (caller receiver : AccountAddress)
    (assets shares ptr cursor1 cursor2 : UInt256) : Frame :=
  cursorResultFrame (erc4626TransferredFrame imms caller receiver assets shares ptr cursor1)
    "__c1" (.tuple []) cursor2

set_option maxRecDepth 2000 in
theorem allocatedDepositFunction_body :
    allocatedDepositFunction.body =
      .internalCall allocatedERC4626DepositFunction.name
        [.var "caller", .var "receiver", .var "assets", .var "shares", .var cursorName] cursorName ::
      depositSupplyStatements ++ depositFinish := by decide +kernel

set_option maxRecDepth 2000 in
theorem allocatedDepositFunction_lookup :
    lookupCallable? contract allocatedDepositFunction.name = some allocatedDepositFunction.toCallable := by rfl

theorem depositERC4626Args (imms : Store) (evm : State) (caller receiver : AccountAddress)
    (assets shares ptr : UInt256) :
    evalExprs? config (erc4626DepositFrame imms caller receiver assets shares ptr) evm
      [.var "caller", .var "receiver", .var "assets", .var "shares", .var cursorName] =
      .ok [.address caller, .address receiver, uint256Value assets, uint256Value shares, uint256Value ptr] := by
  simp [evalExprs?, evalExpr?, erc4626DepositFrame, cursorName,
    Std.HashMap.getElem_insert, EvalResult.ofOption, bind, EvalResult.bind, pure]

set_option maxRecDepth 2000 in
theorem depositERC4626Call {imms : Store} {evm evm' : State} {caller receiver : AccountAddress}
    {assets shares ptr cursor : UInt256} {final : Frame}
    (hbody : ExecFuncBody config (erc4626DepositFrame imms caller receiver assets shares ptr) evm
      allocatedERC4626DepositFunction.body (.returned final evm' (some [uint256Value cursor]))) :
    ExecStmt config (erc4626DepositFrame imms caller receiver assets shares ptr) evm
      (.internalCall allocatedERC4626DepositFunction.name
        [.var "caller", .var "receiver", .var "assets", .var "shares", .var cursorName] cursorName)
      (.ok (erc4626TransferredFrame imms caller receiver assets shares ptr cursor) evm') :=
  internalCallFunctionReturn (callee := allocatedERC4626DepositFunction)
    (caller := erc4626DepositFrame imms caller receiver assets shares ptr)
    (locals := (erc4626DepositFrame imms caller receiver assets shares ptr).locals)
    (value := some [uint256Value cursor])
    (depositERC4626Args imms evm caller receiver assets shares ptr) rfl rfl hbody

set_option maxRecDepth 2000 in
theorem depositERC4626Reverts {imms : Store} {evm : State} {caller receiver : AccountAddress}
    {assets shares ptr : UInt256}
    (hbody : ExecFuncBody config (erc4626DepositFrame imms caller receiver assets shares ptr) evm
      allocatedERC4626DepositFunction.body .reverted) :
    ExecFuncBody config (erc4626DepositFrame imms caller receiver assets shares ptr) evm
      allocatedDepositFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [allocatedDepositFunction_body]
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := allocatedERC4626DepositFunction)
    (depositERC4626Args imms evm caller receiver assets shares ptr) rfl rfl hbody)

theorem depositSupplyArgs (imms : Store) (evm : State) (caller receiver : AccountAddress)
    (assets shares ptr cursor : UInt256) :
    evalExprs? config (erc4626TransferredFrame imms caller receiver assets shares ptr cursor) evm
      [.var "assets", .var cursorName] = .ok [uint256Value assets, uint256Value cursor] := by
  simp [evalExprs?, evalExpr?, erc4626TransferredFrame, erc4626DepositFrame, cursorName,
    Std.HashMap.getElem_insert, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem depositSupplyCall {imms : Store} {evm evm' : State} {caller receiver : AccountAddress}
    {assets shares ptr cursor1 cursor2 : UInt256} {final : Frame}
    (hbody : ExecFuncBody config (allocatedSupplyMorphoFrame imms assets cursor1) evm
      allocatedSupplyMorphoFunction.body (.returned final evm' (some [.tuple [], uint256Value cursor2]))) :
    ExecStmt config (erc4626TransferredFrame imms caller receiver assets shares ptr cursor1) evm
      (.internalCall allocatedSupplyMorphoFunction.name [.var "assets", .var cursorName] slotsAndCursorName)
      (.ok (resumeAfterInternalCall
        (erc4626TransferredFrame imms caller receiver assets shares ptr cursor1) slotsAndCursorName
        (some [.tuple [], uint256Value cursor2])) evm') :=
  internalCallFunctionReturn (callee := allocatedSupplyMorphoFunction)
    (depositSupplyArgs imms evm caller receiver assets shares ptr cursor1)
    allocatedSupplyMorphoFunction_lookup rfl hbody

theorem depositSupplyReverts {imms : Store} {evm : State} {caller receiver : AccountAddress}
    {assets shares ptr cursor : UInt256}
    (hbody : ExecFuncBody config (allocatedSupplyMorphoFrame imms assets cursor) evm
      allocatedSupplyMorphoFunction.body .reverted) :
    ExecBlock config (erc4626TransferredFrame imms caller receiver assets shares ptr cursor) evm
      (depositSupplyStatements ++ depositFinish) .reverted :=
  ExecBlock.consRevert (internalCallFunctionRevert (callee := allocatedSupplyMorphoFunction)
    (depositSupplyArgs imms evm caller receiver assets shares ptr cursor)
    allocatedSupplyMorphoFunction_lookup rfl hbody)

theorem depositSuppliedFrame_assets (imms : Store) (caller receiver : AccountAddress)
    (assets shares ptr cursor1 cursor2 : UInt256) :
    (depositSuppliedFrame imms caller receiver assets shares ptr cursor1 cursor2).locals.get? "assets" =
      some (uint256Value assets) := by
  rw [depositSuppliedFrame, cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
  simp [erc4626TransferredFrame, erc4626DepositFrame, cursorName, Std.HashMap.getElem_insert]

theorem depositSuppliedFrame_lastAssets (imms : Store) (caller receiver : AccountAddress)
    (assets shares ptr cursor1 cursor2 : UInt256) :
    (depositSuppliedFrame imms caller receiver assets shares ptr cursor1 cursor2).locals.get? "lastTotalAssets" =
      none := by
  rw [depositSuppliedFrame, cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
  simp [erc4626TransferredFrame, erc4626DepositFrame, cursorName, Std.HashMap.getElem_insert]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
