import Benchmarks.Morpho.MetaMorphoV1_1.MulticallElementSource

/-! Lift the modular delegatecall result into the multicall source loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

theorem multicallDelegateArgs (frame : Frame) (evm : State) (input : ByteArray) (ptr : UInt256) :
    evalExprs? config (multicallCopyFrame frame input ptr) evm
      [.env .this, .var "__solcDelegateData", .var cursorName] =
        .ok [.address evm.executionEnv.codeOwner, .bytes input,
          uint256Value (bytesAllocPtr ptr input.size)] := by
  simp only [evalExprs?, evalExpr?, envValue, multicallCopyFrame, multicallReadFrame,
    store_get_self, store_get_ne _ _ (show (cursorName == "__solcDelegateData") = false by decide),
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem multicallDelegateReverts {frame : Frame} {imms : Store} {evm : State}
    {data : List Value} {results : List ByteArray} {i : Nat} {ptr : UInt256} {input : ByteArray}
    (h : MulticallReady frame imms data results i ptr) (hv : data[i]? = some (.bytes input))
    (hl : input.size < 2 ^ 64) (hf : allocationFits ptr (UInt256.ofNat (32 + input.size)))
    (hbody : ExecFuncBody config
      (addressCallFrame imms evm.executionEnv.codeOwner input (bytesAllocPtr ptr input.size)) evm
      allocatedDelegateCallFunction.body .reverted) :
    ExecBlock config frame evm multicallLoopBody .reverted := by
  apply (multicallCopyPrefix h hv hl hf).run
  apply ExecBlock.consRevert
  have hc := h.contract
  have him := h.immutables
  rcases frame with ⟨c, locals, imm⟩
  dsimp only at hc him
  subst c
  subst imm
  exact internalCallFunctionRevert (callee := allocatedDelegateCallFunction)
    (multicallDelegateArgs _ evm input ptr) rfl rfl hbody

theorem multicallResultTail {frame : Frame} {imms : Store} {evm : State}
    {data : List Value} {results : List ByteArray} {i : Nat} {ptr : UInt256}
    (h : MulticallReady frame imms data results i ptr) (hi : i < results.length)
    (input out : ByteArray) :
    ExecBlock config (multicallCallFrame frame input ptr out) evm (multicallLoopBody.drop 5)
      (.ok (multicallStepFrame frame input ptr out results i) evm) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .bytes out) ?_) ?_
  · simp only [evalExpr?, multicallCallFrame, store_get_self, EvalResult.ofOption,
      bind, EvalResult.bind, pure, tupleGetValue?, lookupNth?]
    rfl
  refine ExecBlock.consNormal (ExecStmt.letDecl
    (value := uint256Value (callReturnCursor (bytesAllocPtr ptr input.size) out)) ?_) ?_
  · simp only [evalExpr?, store_get_ne _ _ (by decide : ("__c0" == "__solcDelegateResult") = false),
      multicallCallFrame, store_get_self, EvalResult.ofOption,
      bind, EvalResult.bind, pure, tupleGetValue?, lookupNth?]
    rfl
  refine ExecBlock.consNormal (ExecStmt.assign (value := .bytes out)
    (stele' := { multicallResultFrame frame input ptr out with
      locals := (multicallResultFrame frame input ptr out).locals.insert "results"
        (.array ((results.map Value.bytes).set i (.bytes out))) }) (evm' := evm) ?_ ?_) ?_
  · simp only [evalExpr?, store_get_ne _ _ (by decide : (cursorName == "__c0") = false),
      store_get_self, EvalResult.ofOption]
  · apply assignLocalArrayIndex
    · change (multicallResultFrame frame input ptr out).locals.get? "results" = _
      simp only [multicallResultFrame, multicallCallFrame, multicallCopyFrame, multicallReadFrame]
      repeat rw [store_get_ne _ _ (by decide)]
      exact h.results
    · change (multicallResultFrame frame input ptr out).locals.get? "i" = _
      simp only [multicallResultFrame, multicallCallFrame, multicallCopyFrame, multicallReadFrame]
      repeat rw [store_get_ne _ _ (by decide)]
      exact h.index
    · rw [List.length_map]; exact hi
  · simpa only [multicallStepFrame, multicallResultFrame, List.map_set] using
      (ExecBlock.nil (cfg := config) (stele := multicallStepFrame frame input ptr out results i)
        (evm := evm))

theorem multicallDelegateReturns {frame : Frame} {imms : Store} {evm evm' : State}
    {data : List Value} {results : List ByteArray} {i : Nat} {ptr : UInt256} {input out : ByteArray}
    (h : MulticallReady frame imms data results i ptr) (hv : data[i]? = some (.bytes input))
    (hl : input.size < 2 ^ 64) (hf : allocationFits ptr (UInt256.ofNat (32 + input.size)))
    (hi : i < results.length)
    (hbody : ExecFuncBody config
      (addressCallFrame imms evm.executionEnv.codeOwner input (bytesAllocPtr ptr input.size)) evm
      allocatedDelegateCallFunction.body
      (.returned (addressCallResultFrame imms evm.executionEnv.codeOwner input
        (bytesAllocPtr ptr input.size) out) evm'
        (some [.bytes out, uint256Value (callReturnCursor (bytesAllocPtr ptr input.size) out)]))) :
    ExecBlock config frame evm multicallLoopBody
      (.ok (multicallStepFrame frame input ptr out results i) evm') := by
  apply (multicallCopyPrefix h hv hl hf).run
  apply ExecBlock.consNormal _ (multicallResultTail h hi input out)
  have hc := h.contract
  have him := h.immutables
  rcases frame with ⟨c, locals, imm⟩
  dsimp only at hc him
  subst c
  subst imm
  have hcall := internalCallFunctionReturn
    (caller := multicallCopyFrame ⟨contract, locals, imms⟩ input ptr)
    (callee := allocatedDelegateCallFunction) (name := allocatedDelegateCallFunction.name)
    (retVar := "__solcDelegateResult")
    (multicallDelegateArgs _ evm input ptr) rfl rfl hbody
  exact hcall

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
