import Benchmarks.Morpho.MetaMorphoV1_1.MulticallReady

/-! Source execution for a deferred calldata access and its checked copy allocation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def multicallElementGuard : Expr := .binary .ne (.var "__solcDelegateData")
  (.structLit decodeFailureTag [])

theorem multicallElementGuard_false (frame : Frame) (evm : State) :
    evalExpr? config (multicallReadFrame frame decodeFailure) evm multicallElementGuard =
      .ok (.bool false) := by
  simp only [multicallElementGuard, evalExpr?, multicallReadFrame, store_get_self,
    EvalResult.ofOption, evalStructFields?, bind, EvalResult.bind, pure, evalBinaryOp?,
    decodeFailure]
  rfl

theorem multicallElementGuard_true (frame : Frame) (evm : State) (data : ByteArray) :
    evalExpr? config (multicallReadFrame frame (.bytes data)) evm multicallElementGuard =
      .ok (.bool true) := by
  simp only [multicallElementGuard, evalExpr?, multicallReadFrame, store_get_self,
    EvalResult.ofOption, evalStructFields?, bind, EvalResult.bind, pure, evalBinaryOp?]
  rfl

theorem multicallReadReverts {frame : Frame} {imms : Store} {evm : State}
    {data : List Value} {results : List ByteArray} {i : Nat} {ptr : UInt256}
    (h : MulticallReady frame imms data results i ptr) (hv : data[i]? = some decodeFailure) :
    ExecBlock config frame evm multicallLoopBody .reverted := by
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalLocalArrayIndex h.input h.index hv rfl)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (multicallElementGuard_false frame evm))

theorem multicallReadPrefix {frame : Frame} {imms : Store} {evm : State}
    {data : List Value} {results : List ByteArray} {i : Nat} {ptr : UInt256} {input : ByteArray}
    (h : MulticallReady frame imms data results i ptr) (hv : data[i]? = some (.bytes input))
    (hl : input.size < 2 ^ 64) :
    ABlock config evm frame multicallLoopBody (multicallReadFrame frame (.bytes input))
      (multicallLoopBody.drop 3) := by
  refine ((ABlock.start.letStep (evalLocalArrayIndex h.input h.index hv rfl)).requireStep
    (multicallElementGuard_true frame evm input)).requireStep ?_
  exact (evalLocalBytesLengthLt (2 ^ 64) (store_get_self _ _ _)).trans
    (by rw [decide_eq_true hl])

theorem multicallCopySizeSource {frame : Frame} {evm : State} {input : ByteArray}
    (hget : frame.locals.get? "__solcDelegateData" = some (.bytes input))
    (hl : input.size < 2 ^ 64) :
    evalExpr? config frame evm (.binary .add (.intLit 32) multicallDataLength) =
      .ok (uint256Value (UInt256.ofNat (32 + input.size))) := by
  have hs : 32 + input.size < UInt256.size := by change _ < 2 ^ 256; omega
  simpa only [uint256Value, UInt256.toNat_ofNat_of_lt hs] using
    naturalAddSource (show evalExpr? config frame evm (.intLit 32) =
      .ok (.int (Int.ofNat 32)) by simp only [evalExpr?, pure]; rfl)
      (show evalExpr? config frame evm multicallDataLength = .ok (.int (Int.ofNat input.size)) by
        simp only [multicallDataLength, evalExpr?, hget, readLocalPath?, bind, EvalResult.bind, pure])

theorem multicallCopyPrefix {frame : Frame} {imms : Store} {evm : State}
    {data : List Value} {results : List ByteArray} {i : Nat} {ptr : UInt256} {input : ByteArray}
    (h : MulticallReady frame imms data results i ptr) (hv : data[i]? = some (.bytes input))
    (hl : input.size < 2 ^ 64) (hf : allocationFits ptr (UInt256.ofNat (32 + input.size))) :
    ABlock config evm frame multicallLoopBody (multicallCopyFrame frame input ptr)
      (multicallLoopBody.drop 4) := by
  constructor
  intro result htail
  apply (multicallReadPrefix h hv hl).run
  have hc := allocateCallReturns (cfg := config) (frame := multicallReadFrame frame (.bytes input))
    (evm := evm) (ptrExpr := .var cursorName) cursorName
    (by rw [show (multicallReadFrame frame (.bytes input)).contract = contract from h.contract]
        exact allocateFunction_lookup)
    (evalLocalValue (by rw [multicallReadFrame, store_get_ne _ _ (by decide)]; exact h.cursor))
    (multicallCopySizeSource (store_get_self _ _ _) hl) hf
  rw [nextCursor_bytesAlloc] at hc
  exact ExecBlock.consNormal hc htail

theorem multicallCopyReverts {frame : Frame} {imms : Store} {evm : State}
    {data : List Value} {results : List ByteArray} {i : Nat} {ptr : UInt256} {input : ByteArray}
    (h : MulticallReady frame imms data results i ptr) (hv : data[i]? = some (.bytes input))
    (hl : input.size < 2 ^ 64) (hf : ¬ allocationFits ptr (UInt256.ofNat (32 + input.size))) :
    ExecBlock config frame evm multicallLoopBody .reverted := by
  apply (multicallReadPrefix h hv hl).run
  apply ExecBlock.consRevert
  exact allocateCallReverts cursorName
    (by rw [show (multicallReadFrame frame (.bytes input)).contract = contract from h.contract]
        exact allocateFunction_lookup)
    (evalLocalValue (by rw [multicallReadFrame, store_get_ne _ _ (by decide)]; exact h.cursor))
    (multicallCopySizeSource (store_get_self _ _ _) hl) hf

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
