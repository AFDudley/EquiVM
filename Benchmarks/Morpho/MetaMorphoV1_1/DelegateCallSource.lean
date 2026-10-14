import Benchmarks.Morpho.MetaMorphoV1_1.AddressCallSource
import Benchmarks.Morpho.MetaMorphoV1_1.DelegateCallSimulation

/-! Modular source execution of the allocated Address delegate-call helper. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

theorem delegateCallPrefix {evm evm' : State} (imms : Store) (target : AccountAddress)
    (data : ByteArray) (ptr : UInt256) (ok : Bool) (out : ByteArray) {result : ExecResult}
    (hcall : delegateCallViaEVM evm target data (ok, evm', out))
    (htail : ExecBlock config (addressCallRawFrame imms target data ptr ok out) evm'
      addressCallReturnBody result) :
    ExecBlock config (addressCallFrame imms target data ptr) evm
      allocatedDelegateCallFunction.body result := by
  apply ExecBlock.consNormal _ htail
  exact delegateCallSource
    (by simp only [evalExpr?, addressCallFrame, store_get_self, EvalResult.ofOption])
    (by simp [evalExpr?, addressCallFrame, Std.HashMap.getElem_insert, EvalResult.ofOption])
    hcall

theorem delegateCallBodyReturns {evm evm' : State} (imms : Store) (target : AccountAddress)
    (data : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hcall : delegateCallViaEVM evm target data (true, evm', out))
    (hfit : callReturnFits ptr out) (hvalid : addressReturnValid evm' target out) :
    ExecFuncBody config (addressCallFrame imms target data ptr) evm
      allocatedDelegateCallFunction.body
      (.returned (addressCallResultFrame imms target data ptr out) evm'
        (some [.bytes out, uint256Value (callReturnCursor ptr out)])) := by
  apply ExecFuncBody.execBlockRet
  apply delegateCallPrefix imms target data ptr true out hcall
  exact addressCallPostReturns evm' imms target data ptr out hfit hvalid

theorem delegateCallBodyReverts {evm evm' : State} (imms : Store) (target : AccountAddress)
    (data : ByteArray) (ptr : UInt256) (ok : Bool) (out : ByteArray)
    (hcall : delegateCallViaEVM evm target data (ok, evm', out))
    (hbad : ¬ callReturnFits ptr out ∨ ok = false ∨ ¬ addressReturnValid evm' target out) :
    ExecFuncBody config (addressCallFrame imms target data ptr) evm
      allocatedDelegateCallFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply delegateCallPrefix imms target data ptr ok out hcall
  by_cases hfit : callReturnFits ptr out
  · exact addressCallPostRevertsVerify evm' imms target data ptr ok out hfit
      (hbad.resolve_left (not_not_intro hfit))
  · exact addressCallPostRevertsAllocation evm' imms target data ptr ok out hfit

theorem delegateCallStatementReturns {evm evm' : State} (locals imms : Store)
    (target : AccountAddress) (data : ByteArray) (ptr : UInt256) (out : ByteArray)
    (args : List Expr) (retVar : Ident)
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address target, .bytes data, uint256Value ptr])
    (hcall : delegateCallViaEVM evm target data (true, evm', out))
    (hfit : callReturnFits ptr out) (hvalid : addressReturnValid evm' target out) :
    ExecStmt config ⟨contract, locals, imms⟩ evm
      (.internalCall allocatedDelegateCallFunction.name args retVar)
      (.ok ⟨contract, locals.insert retVar
        (.tuple [.bytes out, uint256Value (callReturnCursor ptr out)]), imms⟩ evm') :=
  internalCallFunctionReturn (callee := allocatedDelegateCallFunction) hargs rfl rfl
    (delegateCallBodyReturns imms target data ptr out hcall hfit hvalid)

theorem delegateCallStatementReverts {evm evm' : State} (locals imms : Store)
    (target : AccountAddress) (data : ByteArray) (ptr : UInt256) (ok : Bool) (out : ByteArray)
    (args : List Expr) (retVar : Ident)
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address target, .bytes data, uint256Value ptr])
    (hcall : delegateCallViaEVM evm target data (ok, evm', out))
    (hbad : ¬ callReturnFits ptr out ∨ ok = false ∨ ¬ addressReturnValid evm' target out) :
    ExecStmt config ⟨contract, locals, imms⟩ evm
      (.internalCall allocatedDelegateCallFunction.name args retVar) .reverted :=
  internalCallFunctionRevert (callee := allocatedDelegateCallFunction) hargs rfl rfl
    (delegateCallBodyReverts imms target data ptr ok out hcall hbad)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
