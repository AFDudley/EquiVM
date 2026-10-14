import Benchmarks.Morpho.MetaMorphoV1_1.SafeTransferFromSource
import Benchmarks.Morpho.MetaMorphoV1_1.MintInternalSource

/-! Source composition of transferFrom, share minting, and the Deposit event. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def erc4626DepositFrame (imms : Store) (caller receiver : AccountAddress)
    (assets shares ptr : UInt256) : Frame :=
  ⟨contract, (((((∅ : Store).insert cursorName (uint256Value ptr)).insert
    "shares" (uint256Value shares)).insert "assets" (uint256Value assets)).insert
    "receiver" (.address receiver)).insert "caller" (.address caller), imms⟩

def erc4626TransferredFrame (imms : Store) (caller receiver : AccountAddress)
    (assets shares ptr cursor : UInt256) : Frame :=
  let f := erc4626DepositFrame imms caller receiver assets shares ptr
  { f with locals := f.locals.insert cursorName (uint256Value cursor) }

def erc4626DepositResultFrame (imms : Store) (caller receiver : AccountAddress)
    (assets shares ptr cursor : UInt256) : Frame :=
  let f := erc4626TransferredFrame imms caller receiver assets shares ptr cursor
  { f with locals := f.locals.insert "__c1" .unit }

def erc4626DepositMintTail : List Stmt :=
  [.internalCall "_mint" [.var "receiver", .var "shares"] "__c1",
   .emit "Deposit" [.var "caller", .var "receiver", .var "assets", .var "shares"],
   .return [.var cursorName]]

theorem allocatedERC4626DepositFunction_body :
    allocatedERC4626DepositFunction.body =
      .internalCall allocatedSafeTransferFromFunction.name
        [.immutable "_asset", .var "caller", .env .this, .var "assets", .var cursorName]
        cursorName :: erc4626DepositMintTail := by decide +kernel

theorem erc4626DepositTransferArgs (v : MetaMorphoV1_1Immutables) (evm : State)
    (caller receiver : AccountAddress) (assets shares ptr : UInt256) :
    evalExprs? config (erc4626DepositFrame (immStore v) caller receiver assets shares ptr) evm
      [.immutable "_asset", .var "caller", .env .this, .var "assets", .var cursorName] =
      .ok [.address v._asset, .address caller, .address evm.executionEnv.codeOwner,
        uint256Value assets, uint256Value ptr] := by
  simp [evalExprs?, evalExpr?, erc4626DepositFrame, immStore, envValue, cursorName,
    Std.HashMap.getElem_insert, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem erc4626DepositTransferPrefix {evm evm' : State} {final : Frame}
    (v : MetaMorphoV1_1Immutables) (caller receiver : AccountAddress)
    (assets shares ptr cursor : UInt256)
    (hcall : ExecFuncBody config
      (safeTransferFromFrame (immStore v) v._asset caller evm.executionEnv.codeOwner assets ptr)
      evm allocatedSafeTransferFromFunction.body (.returned final evm' [uint256Value cursor]))
    {result : ExecResult}
    (htail : ExecBlock config
      (erc4626TransferredFrame (immStore v) caller receiver assets shares ptr cursor) evm'
      erc4626DepositMintTail result) :
    ExecBlock config (erc4626DepositFrame (immStore v) caller receiver assets shares ptr)
      evm allocatedERC4626DepositFunction.body result := by
  rw [allocatedERC4626DepositFunction_body]
  exact ExecBlock.consNormal (internalCallFunctionReturn
    (callee := allocatedSafeTransferFromFunction)
    (erc4626DepositTransferArgs v evm caller receiver assets shares ptr) rfl rfl hcall) htail

theorem erc4626DepositTransferReverts {evm : State}
    (v : MetaMorphoV1_1Immutables) (caller receiver : AccountAddress) (assets shares ptr : UInt256)
    (hcall : ExecFuncBody config
      (safeTransferFromFrame (immStore v) v._asset caller evm.executionEnv.codeOwner assets ptr)
      evm allocatedSafeTransferFromFunction.body .reverted) :
    ExecFuncBody config (erc4626DepositFrame (immStore v) caller receiver assets shares ptr)
      evm allocatedERC4626DepositFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [allocatedERC4626DepositFunction_body]
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := allocatedSafeTransferFromFunction)
    (erc4626DepositTransferArgs v evm caller receiver assets shares ptr) rfl rfl hcall)

theorem erc4626DepositMintArgs (evm : State) (imms : Store) (caller receiver : AccountAddress)
    (assets shares ptr cursor : UInt256) :
    evalExprs? config (erc4626TransferredFrame imms caller receiver assets shares ptr cursor) evm
      [.var "receiver", .var "shares"] = .ok [.address receiver, uint256Value shares] := by
  simp [evalExprs?, evalExpr?, erc4626TransferredFrame, erc4626DepositFrame, cursorName,
    Std.HashMap.getElem_insert, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem erc4626DepositMintReturns (evm : State) (imms : Store) (caller receiver : AccountAddress)
    (assets shares ptr cursor : UInt256) (hgood : mintAllowed evm receiver shares) :
    ExecBlock config (erc4626TransferredFrame imms caller receiver assets shares ptr cursor) evm
      erc4626DepositMintTail
      (.returned (erc4626DepositResultFrame imms caller receiver assets shares ptr cursor)
        (mintBalanceState evm receiver shares) [uint256Value cursor]) := by
  apply ExecBlock.consNormal
    (mintCall (erc4626DepositMintArgs evm imms caller receiver assets shares ptr cursor) hgood)
  apply ExecBlock.consNormal (ExecStmt.emit
    (vals := [.address caller, .address receiver, uint256Value assets, uint256Value shares]) ?_)
  · apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp [evalExprs?, evalExpr?, resumeAfterInternalCall, erc4626TransferredFrame,
      erc4626DepositFrame, collapseReturns, cursorName, Std.HashMap.getElem_insert,
      EvalResult.ofOption, bind, EvalResult.bind, pure]
  · simp [evalExprs?, evalExpr?, resumeAfterInternalCall, erc4626TransferredFrame,
      erc4626DepositFrame, collapseReturns, cursorName, Std.HashMap.getElem_insert,
      EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem erc4626DepositMintReverts (evm : State) (imms : Store) (caller receiver : AccountAddress)
    (assets shares ptr cursor : UInt256) (hbad : ¬ mintAllowed evm receiver shares) :
    ExecBlock config (erc4626TransferredFrame imms caller receiver assets shares ptr cursor) evm
      erc4626DepositMintTail .reverted :=
  ExecBlock.consRevert
    (mintCallReverts (erc4626DepositMintArgs evm imms caller receiver assets shares ptr cursor) hbad)

theorem erc4626DepositMintStatic (evm : State) (imms : Store) (caller receiver : AccountAddress)
    (assets shares ptr cursor : UInt256) (hgood : mintAllowed evm receiver shares)
    (hperm : evm.executionEnv.perm = false) :
    ExecBlock config (erc4626TransferredFrame imms caller receiver assets shares ptr cursor) evm
      erc4626DepositMintTail .staticViolation :=
  ExecBlock.consStatic
    (mintCallStatic (erc4626DepositMintArgs evm imms caller receiver assets shares ptr cursor) hgood hperm)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
