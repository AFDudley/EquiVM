import Benchmarks.Morpho.MetaMorphoV1_1.BurnInternalSource
import Benchmarks.Morpho.MetaMorphoV1_1.SpendAllowanceCalls
import Benchmarks.Morpho.MetaMorphoV1_1.SafeTransferSource

/-! Source statements and caller locals across allowance spending, burning, and payment. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def erc4626WithdrawFrame (imms : Store) (caller receiver owner : AccountAddress)
    (assets shares ptr : UInt256) : Frame :=
  ⟨contract, ((((((∅ : Store).insert cursorName (uint256Value ptr)).insert
    "shares" (uint256Value shares)).insert "assets" (uint256Value assets)).insert
    "owner" (.address owner)).insert "receiver" (.address receiver)).insert "caller" (.address caller), imms⟩

def erc4626WithdrawAllowance : Stmt :=
  .ite (.binary .ne (.var "caller") (.var "owner"))
    [.internalCall "_spendAllowance" [.var "owner", .var "caller", .var "shares"] "__c0"] []

def erc4626WithdrawBurn : Stmt :=
  .internalCall "_burn" [.var "owner", .var "shares"] "__c1"

def erc4626WithdrawTransfer : Stmt :=
  .internalCall allocatedSafeTransferFunction.name
    [.immutable "_asset", .var "receiver", .var "assets", .var cursorName] cursorName

def erc4626WithdrawFinish : List Stmt :=
  [.emit "Withdraw" [.var "caller", .var "receiver", .var "owner", .var "assets", .var "shares"],
   .return [.var cursorName]]

theorem allocatedERC4626WithdrawFunction_body :
    allocatedERC4626WithdrawFunction.body = erc4626WithdrawAllowance :: erc4626WithdrawBurn ::
      erc4626WithdrawTransfer :: erc4626WithdrawFinish := by decide +kernel

structure WithdrawVaultLocals (v : MetaMorphoV1_1Immutables) (frame : Frame)
    (caller receiver owner : AccountAddress) (assets shares cursor : UInt256) : Prop where
  contract : frame.contract = contract
  imms : frame.immutables = immStore v
  caller : frame.locals.get? "caller" = some (.address caller)
  receiver : frame.locals.get? "receiver" = some (.address receiver)
  owner : frame.locals.get? "owner" = some (.address owner)
  assets : frame.locals.get? "assets" = some (uint256Value assets)
  shares : frame.locals.get? "shares" = some (uint256Value shares)
  cursor : frame.locals.get? cursorName = some (uint256Value cursor)

theorem erc4626WithdrawInitialLocals (v : MetaMorphoV1_1Immutables) (caller receiver owner : AccountAddress)
    (assets shares ptr : UInt256) :
    WithdrawVaultLocals v (erc4626WithdrawFrame (immStore v) caller receiver owner assets shares ptr)
      caller receiver owner assets shares ptr := by
  constructor <;> simp [erc4626WithdrawFrame, cursorName, Std.HashMap.getElem_insert]

theorem WithdrawVaultLocals.insert {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {caller receiver owner : AccountAddress} {assets shares cursor : UInt256}
    (h : WithdrawVaultLocals v frame caller receiver owner assets shares cursor)
    (name : Ident) (value : Value)
    (hc : (name == "caller") = false) (hr : (name == "receiver") = false)
    (ho : (name == "owner") = false) (ha : (name == "assets") = false)
    (hs : (name == "shares") = false) (hp : (name == cursorName) = false) :
    WithdrawVaultLocals v { frame with locals := frame.locals.insert name value }
      caller receiver owner assets shares cursor := by
  refine ⟨h.contract, h.imms, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (store_get_ne _ _ hc).trans h.caller
  · exact (store_get_ne _ _ hr).trans h.receiver
  · exact (store_get_ne _ _ ho).trans h.owner
  · exact (store_get_ne _ _ ha).trans h.assets
  · exact (store_get_ne _ _ hs).trans h.shares
  · exact (store_get_ne _ _ hp).trans h.cursor

theorem WithdrawVaultLocals.withCursor {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {caller receiver owner : AccountAddress} {assets shares cursor : UInt256}
    (h : WithdrawVaultLocals v frame caller receiver owner assets shares cursor) (ptr : UInt256) :
    WithdrawVaultLocals v { frame with locals := frame.locals.insert cursorName (uint256Value ptr) }
      caller receiver owner assets shares ptr := by
  refine ⟨h.contract, h.imms, ?_, ?_, ?_, ?_, ?_, store_get_self _ _ _⟩
  · exact (store_get_ne _ _ (by decide)).trans h.caller
  · exact (store_get_ne _ _ (by decide)).trans h.receiver
  · exact (store_get_ne _ _ (by decide)).trans h.owner
  · exact (store_get_ne _ _ (by decide)).trans h.assets
  · exact (store_get_ne _ _ (by decide)).trans h.shares

theorem withdrawVaultAllowanceCondition {v : MetaMorphoV1_1Immutables} {frame : Frame} {evm : State}
    {caller receiver owner : AccountAddress} {assets shares cursor : UInt256}
    (h : WithdrawVaultLocals v frame caller receiver owner assets shares cursor) :
    evalExpr? config frame evm (.binary .ne (.var "caller") (.var "owner")) =
      .ok (.bool (decide (caller ≠ owner))) :=
  evalExpr_addressNe
    (by simp only [evalExpr?, h.caller, EvalResult.ofOption])
    (by simp only [evalExpr?, h.owner, EvalResult.ofOption])

theorem withdrawVaultAllowanceArgs {v : MetaMorphoV1_1Immutables} {frame : Frame} {evm : State}
    {caller receiver owner : AccountAddress} {assets shares cursor : UInt256}
    (h : WithdrawVaultLocals v frame caller receiver owner assets shares cursor) :
    evalExprs? config frame evm [.var "owner", .var "caller", .var "shares"] =
      .ok [.address owner, .address caller, uint256Value shares] := by
  simp only [evalExprs?, evalExpr?, h.owner, h.caller, h.shares,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem withdrawVaultBurnArgs {v : MetaMorphoV1_1Immutables} {frame : Frame} {evm : State}
    {caller receiver owner : AccountAddress} {assets shares cursor : UInt256}
    (h : WithdrawVaultLocals v frame caller receiver owner assets shares cursor) :
    evalExprs? config frame evm [.var "owner", .var "shares"] =
      .ok [.address owner, uint256Value shares] := by
  simp only [evalExprs?, evalExpr?, h.owner, h.shares, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem withdrawVaultTransferArgs {v : MetaMorphoV1_1Immutables} {frame : Frame} {evm : State}
    {caller receiver owner : AccountAddress} {assets shares cursor : UInt256}
    (h : WithdrawVaultLocals v frame caller receiver owner assets shares cursor) :
    evalExprs? config frame evm [.immutable "_asset", .var "receiver", .var "assets", .var cursorName] =
      .ok [.address v._asset, .address receiver, uint256Value assets, uint256Value cursor] := by
  have hi : evalExpr? config frame evm (.immutable "_asset") = .ok (.address v._asset) := by
    simp only [evalExpr?, h.imms, immStore_get__asset, EvalResult.ofOption]
  simp only [evalExprs?, hi, evalExpr?, h.receiver, h.assets, h.cursor,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem withdrawVaultFinishSource {v : MetaMorphoV1_1Immutables} {frame : Frame} {evm : State}
    {caller receiver owner : AccountAddress} {assets shares cursor : UInt256}
    (h : WithdrawVaultLocals v frame caller receiver owner assets shares cursor) :
    ExecBlock config frame evm erc4626WithdrawFinish (.returned frame evm [uint256Value cursor]) := by
  apply ExecBlock.consNormal (ExecStmt.emit
    (vals := [.address caller, .address receiver, .address owner, uint256Value assets, uint256Value shares]) ?_)
  · apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp only [evalExprs?, evalExpr?, h.cursor, EvalResult.ofOption, bind, EvalResult.bind, pure]
  · simp only [evalExprs?, evalExpr?, h.caller, h.receiver, h.owner, h.assets, h.shares,
      EvalResult.ofOption, bind, EvalResult.bind, pure]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
