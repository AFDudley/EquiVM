import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSource
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateRowABI
import Benchmarks.EAS.Attester.LocalArray

/-! Strict two-word external returns and their checked memory reservation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def strictPairCallValue (out : ByteArray) : Value :=
  .tuple [uint256Value (calldataWord out 0), uint256Value (calldataWord out 32)]

def strictPairCallFrame (frame : Frame) (retVar : Ident) (ptr : UInt256) (out : ByteArray) : Frame :=
  { frame with locals := ((frame.locals.insert retVar (strictPairCallValue out)).insert
      cursorName (uint256Value (nextCursor ptr ⟨64⟩))) }

-- LIBRARY CANDIDATE: a decoded pair and its fixed-size compiler allocation.
theorem strictPairCallSuccess {frame : Frame} {evm evm' : State} {target : AccountAddress}
    {receiver : Expr} {args : List Expr} {argVals : List Value} {name retVar : Ident}
    {ptr : UInt256} {out : ByteArray}
    (hc : frame.contract = contract) (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hn : (retVar == cursorName) = false)
    (ht : evalExpr? config frame evm receiver = .ok (.address target))
    (ha : evalExprs? config frame evm args = .ok argVals)
    (hcall : typedCallViaEVM config evm target name 0 argVals (true, evm', out))
    (hdecode : config.externalABI.decode? name out =
      some [uint256Value (calldataWord out 0), uint256Value (calldataWord out 32)])
    (hfit : allocationFits ptr ⟨64⟩) :
    ExecBlock config frame evm
      [.externalCall receiver name (.intLit 0) args retVar true, reserveBytes 64]
      (.ok (strictPairCallFrame frame retVar ptr out) evm') := by
  have htgt : EVM.address (target : Nat) = target := evm_address_of_address_toNat target
  refine ExecBlock.consNormal (ExecStmt.externalCallSuccess (sendVal := 0) ht
    (by simp only [evalExpr?, pure]) ha (by rw [htgt]; exact hcall) hdecode) ?_
  refine ExecBlock.consNormal (allocateCallReturns cursorName
    (by change lookupCallable? frame.contract _ = _; rw [hc]; exact allocateFunction_lookup)
    (show evalExpr? config { frame with locals := frame.locals.insert retVar (strictPairCallValue out) }
      evm' (.var cursorName) = .ok (uint256Value ptr) from
        evalLocalValue (by rw [store_get_ne _ _ hn]; exact hp))
    (by simp only [evalExpr?, pure]; rfl) hfit) ExecBlock.nil

-- LIBRARY CANDIDATE: strict-call failure, malformed pair return, or failed return reservation.
theorem strictPairCallRevert {frame : Frame} {evm evm' : State} {target : AccountAddress}
    {receiver : Expr} {args : List Expr} {argVals : List Value} {name retVar : Ident}
    {ptr : UInt256} {out : ByteArray} {ok : Bool}
    (hc : frame.contract = contract) (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hn : (retVar == cursorName) = false)
    (ht : evalExpr? config frame evm receiver = .ok (.address target))
    (ha : evalExprs? config frame evm args = .ok argVals)
    (hcall : typedCallViaEVM config evm target name 0 argVals (ok, evm', out))
    (hdecode : config.externalABI.decode? name out = if 64 ≤ out.size then
      some [uint256Value (calldataWord out 0), uint256Value (calldataWord out 32)] else none)
    (hbad : ok = false ∨ ¬ (64 ≤ out.size ∧ allocationFits ptr ⟨64⟩)) :
    ExecBlock config frame evm
      [.externalCall receiver name (.intLit 0) args retVar true, reserveBytes 64] .reverted := by
  have htgt : EVM.address (target : Nat) = target := evm_address_of_address_toNat target
  cases ok with
  | false =>
      exact ExecBlock.consRevert (ExecStmt.externalCallFailure (sendVal := 0) ht
        (by simp only [evalExpr?, pure]) ha (by rw [htgt]; exact hcall))
  | true =>
      have hb := hbad.resolve_left (by decide)
      by_cases hlong : 64 ≤ out.size
      · rw [if_pos hlong] at hdecode
        refine ExecBlock.consNormal (ExecStmt.externalCallSuccess (sendVal := 0) ht
          (by simp only [evalExpr?, pure]) ha (by rw [htgt]; exact hcall) hdecode) ?_
        apply ExecBlock.consRevert
        exact allocateCallReverts cursorName
          (by change lookupCallable? frame.contract _ = _; rw [hc]; exact allocateFunction_lookup)
          (show evalExpr? config { frame with locals := frame.locals.insert retVar (strictPairCallValue out) }
            evm' (.var cursorName) = .ok (uint256Value ptr) from
              evalLocalValue (by rw [store_get_ne _ _ hn]; exact hp))
          (by simp only [evalExpr?, pure]; rfl) (fun hf ↦ hb ⟨hlong, hf⟩)
      · exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert (sendVal := 0) ht
          (by simp only [evalExpr?, pure]) ha (by rw [htgt]; exact hcall)
          (by rw [hdecode, if_neg hlong]))

theorem strictPairCallFrame_value (frame : Frame) (retVar : Ident) (ptr : UInt256) (out : ByteArray)
    (hn : (cursorName == retVar) = false) :
    (strictPairCallFrame frame retVar ptr out).locals.get? retVar = some (strictPairCallValue out) := by
  rw [strictPairCallFrame, store_get_ne _ _ hn, store_get_self]

theorem strictPairCallFrame_cursor (frame : Frame) (retVar : Ident) (ptr : UInt256) (out : ByteArray) :
    (strictPairCallFrame frame retVar ptr out).locals.get? cursorName =
      some (uint256Value (nextCursor ptr ⟨64⟩)) := store_get_self _ _ _

theorem strictPairCallFrame_preserves (frame : Frame) (retVar : Ident) (ptr : UInt256) (out : ByteArray)
    (name : Ident) (hc : (cursorName == name) = false) (hr : (retVar == name) = false) :
    (strictPairCallFrame frame retVar ptr out).locals.get? name = frame.locals.get? name := by
  rw [strictPairCallFrame, store_get_ne _ _ hc, store_get_ne _ _ hr]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
