import Benchmarks.Morpho.MetaMorphoV1_1.EncodedOptionalCallSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.OptionalCallSource

/-! General source execution for an encoded SafeERC20 request wrapper. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def encodedOptionalDataFrame (frame : Frame) (data : ByteArray) : Frame :=
  { frame with locals := frame.locals.insert "data" (.bytes data) }

def encodedOptionalAllocatedFrame (frame : Frame) (data : ByteArray) (ptr size : UInt256) : Frame :=
  { frame with
    locals := (frame.locals.insert "data" (.bytes data)).insert
      cursorName (uint256Value (nextCursor ptr size)) }

def encodedOptionalResultFrame (frame : Frame) (data : ByteArray) (ptr size cursor : UInt256) : Frame :=
  let f := encodedOptionalAllocatedFrame frame data ptr size
  { f with locals := f.locals.insert "__c0" (uint256Value cursor) }

theorem encodedOptionalArgs {frame : Frame} (evm : State) (data : ByteArray) (ptr size : UInt256)
    {token : AccountAddress} (ht : frame.locals.get? "token" = some (.address token)) :
    evalExprs? config (encodedOptionalAllocatedFrame frame data ptr size) evm
      [.var "token", .var "data", .var cursorName] =
        .ok [.address token, .bytes data, uint256Value (nextCursor ptr size)] := by
  simp only [evalExprs?, evalExpr?, encodedOptionalAllocatedFrame,
    store_get_ne _ _ (by decide : (cursorName == "token") = false),
    store_get_ne _ _ (by decide : ("data" == "token") = false),
    store_get_ne _ _ (by decide : (cursorName == "data") = false), store_get_self, ht,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem encodedOptionalPrefix {frame : Frame} {evm : State} {data : ByteArray}
    {ptr size : UInt256} {encode : Expr} (hc : frame.contract = contract)
    (he : evalExpr? config frame evm encode = .ok (.bytes data))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr)) (hf : allocationFits ptr size) :
    ABlock config evm frame (encodedOptionalCallBody encode size)
      (encodedOptionalAllocatedFrame frame data ptr size)
      ((encodedOptionalCallBody encode size).drop 2) := by
  constructor
  intro result htail
  refine ExecBlock.consNormal (ExecStmt.letDecl he) ?_
  exact ExecBlock.consNormal (allocateCallReturns cursorName (by rw [hc]; exact allocateFunction_lookup)
    (by simp only [evalExpr?, store_get_ne _ _ (by decide : ("data" == cursorName) = false),
          hp, EvalResult.ofOption])
    (by simp only [evalExpr?, pure, uint256Value]) hf) htail

theorem encodedOptionalReturns {frame final : Frame} {evm evm' : State} {data : ByteArray}
    {ptr size cursor : UInt256} {encode : Expr} {token : AccountAddress}
    (hc : frame.contract = contract) (he : evalExpr? config frame evm encode = .ok (.bytes data))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (ht : frame.locals.get? "token" = some (.address token)) (hf : allocationFits ptr size)
    (hcall : ExecFuncBody config
      (optionalCallFrame frame.immutables token data (nextCursor ptr size)) evm
      allocatedOptionalReturnFunction.body (.returned final evm' (some [uint256Value cursor]))) :
    ExecFuncBody config frame evm (encodedOptionalCallBody encode size)
      (.returned (encodedOptionalResultFrame frame data ptr size cursor) evm'
        (some [uint256Value cursor])) := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hc
  subst c
  apply ExecFuncBody.execBlockRet
  apply (encodedOptionalPrefix rfl he hp hf).run
  refine ExecBlock.consNormal (internalCallFunctionReturn (callee := allocatedOptionalReturnFunction)
    (encodedOptionalArgs evm data ptr size ht) rfl rfl hcall) ?_
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  change evalExprs? config
    (encodedOptionalResultFrame ⟨contract, locals, imms⟩ data ptr size cursor) evm' _ = _
  simp only [evalExprs?, evalExpr?, encodedOptionalResultFrame, store_get_self, EvalResult.ofOption,
    bind, EvalResult.bind, pure]

theorem encodedOptionalRevertsCall {frame : Frame} {evm : State} {data : ByteArray}
    {ptr size : UInt256} {encode : Expr} {token : AccountAddress}
    (hc : frame.contract = contract) (he : evalExpr? config frame evm encode = .ok (.bytes data))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (ht : frame.locals.get? "token" = some (.address token)) (hf : allocationFits ptr size)
    (hcall : ExecFuncBody config
      (optionalCallFrame frame.immutables token data (nextCursor ptr size)) evm
      allocatedOptionalReturnFunction.body .reverted) :
    ExecFuncBody config frame evm (encodedOptionalCallBody encode size) .reverted := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hc
  subst c
  apply ExecFuncBody.execBlockRevert
  apply (encodedOptionalPrefix rfl he hp hf).run
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := allocatedOptionalReturnFunction)
    (encodedOptionalArgs evm data ptr size ht) rfl rfl hcall)

theorem encodedOptionalRevertsAllocation {frame : Frame} {evm : State} {data : ByteArray}
    {ptr size : UInt256} {encode : Expr} (hc : frame.contract = contract)
    (he : evalExpr? config frame evm encode = .ok (.bytes data))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr)) (hf : ¬ allocationFits ptr size) :
    ExecFuncBody config frame evm (encodedOptionalCallBody encode size) .reverted := by
  apply ExecFuncBody.execBlockRevert
  refine ExecBlock.consNormal (ExecStmt.letDecl he) ?_
  exact ExecBlock.consRevert (allocateCallReverts cursorName (by rw [hc]; exact allocateFunction_lookup)
    (by simp only [evalExpr?, store_get_ne _ _ (by decide : ("data" == cursorName) = false),
          hp, EvalResult.ofOption])
    (by simp only [evalExpr?, pure, uint256Value]) hf)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
