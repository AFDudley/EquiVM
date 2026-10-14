import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateCallSource
import Benchmarks.Morpho.MetaMorphoV1_1.ApprovalCalls

/-! Decode the withdrawal result, emit its event, and check the running withdrawn total. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
attribute [local irreducible] contract

def reallocateWithdrawEventFrame (frame : Frame) (out : ByteArray) (sender : AccountAddress) : Frame :=
  { frame with locals := (((frame.locals.insert "withdrawnAssets" (uint256Value (calldataWord out 0))).insert
      "withdrawnShares" (uint256Value (calldataWord out 32))).insert "__c6" (.address sender)) }

def reallocateWithdrawFinishFrame (frame : Frame) (out : ByteArray)
    (sender : AccountAddress) (total : UInt256) : Frame :=
  { frame with locals := ((reallocateWithdrawEventFrame frame out sender).locals.insert
      "totalWithdrawn" (uint256Value (total + calldataWord out 0))) }

set_option maxRecDepth 2000 in
theorem reallocateWithdrawEventPrefix {frame : Frame} {evm : State} {out : ByteArray}
    (hc : frame.contract = contract)
    (hret : frame.locals.get? "__c5" = some (strictPairCallValue out)) :
    ABlock config evm frame (reallocateWithdrawBody.drop 4)
      (reallocateWithdrawEventFrame frame out evm.executionEnv.source) (reallocateWithdrawBody.drop 7) := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hc
  subst c
  constructor
  intro result htail
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value (calldataWord out 0)) ?_) ?_
  · simp only [evalExpr?, hret, EvalResult.ofOption, strictPairCallValue,
      bind, EvalResult.bind, tupleGetValue?, List.getElem?_cons_zero]
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value (calldataWord out 32)) ?_) ?_
  · simp only [evalExpr?, store_get_ne _ _ (by decide : ("withdrawnAssets" == "__c5") = false),
      hret, EvalResult.ofOption, strictPairCallValue, bind, EvalResult.bind,
      tupleGetValue?, List.getElem?_cons_zero, List.getElem?_cons_succ]
  exact ExecBlock.consNormal (msgSenderCall _ _ evm "__c6") htail

theorem reallocateWithdrawEventFrame_preserves (frame : Frame) (out : ByteArray) (sender : AccountAddress)
    (name : Ident) (hc : ("__c6" == name) = false) (ha : ("withdrawnAssets" == name) = false)
    (hs : ("withdrawnShares" == name) = false) :
    (reallocateWithdrawEventFrame frame out sender).locals.get? name = frame.locals.get? name := by
  rw [reallocateWithdrawEventFrame, store_get_ne _ _ hc, store_get_ne _ _ hs, store_get_ne _ _ ha]

theorem reallocateWithdrawEventArgs {frame : Frame} {evm : State} {id : UInt256} (out : ByteArray)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id)) :
    evalExprs? config (reallocateWithdrawEventFrame frame out evm.executionEnv.source) evm
      [.var "__c6", .var "id", .var "withdrawnAssets", .var "withdrawnShares"] =
      .ok [.address evm.executionEnv.source, wordBytes32Value id,
        uint256Value (calldataWord out 0), uint256Value (calldataWord out 32)] := by
  simp only [evalExprs?, evalExpr?, reallocateWithdrawEventFrame, store_get_self,
    store_get_ne _ _ (by decide : ("__c6" == "id") = false),
    store_get_ne _ _ (by decide : ("withdrawnAssets" == "id") = false),
    store_get_ne _ _ (by decide : ("withdrawnShares" == "id") = false),
    store_get_ne _ _ (by decide : ("__c6" == "withdrawnAssets") = false),
    store_get_ne _ _ (by decide : ("__c6" == "withdrawnShares") = false),
    store_get_ne _ _ (by decide : ("withdrawnShares" == "withdrawnAssets") = false),
    hid, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem reallocateWithdrawEventAmount (frame : Frame) (evm : State) (out : ByteArray) :
    evalExpr? config (reallocateWithdrawEventFrame frame out evm.executionEnv.source) evm
      (.var "withdrawnAssets") = .ok (uint256Value (calldataWord out 0)) := by
  simp only [evalExpr?, reallocateWithdrawEventFrame,
    store_get_ne _ _ (by decide : ("__c6" == "withdrawnAssets") = false),
    store_get_ne _ _ (by decide : ("withdrawnShares" == "withdrawnAssets") = false),
    store_get_self, EvalResult.ofOption]

theorem reallocateWithdrawFinishSource {frame : Frame} {evm : State} {out : ByteArray} {total id : UInt256}
    (hc : frame.contract = contract)
    (hret : frame.locals.get? "__c5" = some (strictPairCallValue out))
    (ht : frame.locals.get? "totalWithdrawn" = some (uint256Value total))
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hfit : total.toNat + (calldataWord out 0).toNat < UInt256.size) :
    ExecBlock config frame evm (reallocateWithdrawBody.drop 4)
      (.ok (reallocateWithdrawFinishFrame frame out evm.executionEnv.source total) evm) := by
  have htotal : (reallocateWithdrawEventFrame frame out evm.executionEnv.source).locals.get? "totalWithdrawn" =
      some (uint256Value total) := by
    rw [reallocateWithdrawEventFrame_preserves _ _ _ _ (by decide) (by decide) (by decide)]; exact ht
  apply (reallocateWithdrawEventPrefix hc hret).run
  refine ExecBlock.consNormal (ExecStmt.emit (reallocateWithdrawEventArgs out hid)) ?_
  exact ExecBlock.consNormal (ExecStmt.assign
    (checkedAddSourceOk (evalLocalValue htotal) (reallocateWithdrawEventAmount _ _ _) hfit)
    (assignLocalValue htotal)) ExecBlock.nil

theorem reallocateWithdrawFinishRevert {frame : Frame} {evm : State} {out : ByteArray} {total id : UInt256}
    (hc : frame.contract = contract)
    (hret : frame.locals.get? "__c5" = some (strictPairCallValue out))
    (ht : frame.locals.get? "totalWithdrawn" = some (uint256Value total))
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hbad : UInt256.size ≤ total.toNat + (calldataWord out 0).toNat) :
    ExecBlock config frame evm (reallocateWithdrawBody.drop 4) .reverted := by
  have htotal : (reallocateWithdrawEventFrame frame out evm.executionEnv.source).locals.get? "totalWithdrawn" =
      some (uint256Value total) := by
    rw [reallocateWithdrawEventFrame_preserves _ _ _ _ (by decide) (by decide) (by decide)]; exact ht
  apply (reallocateWithdrawEventPrefix hc hret).run
  refine ExecBlock.consNormal (ExecStmt.emit (reallocateWithdrawEventArgs out hid)) ?_
  exact ExecBlock.consRevert (ExecStmt.assignExprRevert
    (checkedAddSourceOverflow (evalLocalValue htotal) (reallocateWithdrawEventAmount _ _ _) hbad))

theorem reallocateWithdrawFinishStatic {frame : Frame} {evm : State} {out : ByteArray} {id : UInt256}
    (hc : frame.contract = contract)
    (hret : frame.locals.get? "__c5" = some (strictPairCallValue out))
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hperm : evm.executionEnv.perm = false) :
    ExecBlock config frame evm (reallocateWithdrawBody.drop 4) .staticViolation := by
  apply (reallocateWithdrawEventPrefix hc hret).run
  exact ExecBlock.consStatic (ExecStmt.emitStatic (reallocateWithdrawEventArgs out hid) hperm)

theorem ReallocateLocals.withdrawFinish {v : MetaMorphoV1_1Immutables} {frame : Frame} {values : List Value}
    {i supplied withdrawn cursor : UInt256} (h : ReallocateLocals v frame values i supplied withdrawn cursor)
    (out : ByteArray) (sender : AccountAddress) :
    ReallocateLocals v (reallocateWithdrawFinishFrame frame out sender withdrawn) values i
      supplied (withdrawn + calldataWord out 0) cursor :=
  (((h.insert "withdrawnAssets" (uint256Value (calldataWord out 0)) (by decide)).insert
    "withdrawnShares" (uint256Value (calldataWord out 32)) (by decide)).insert
      "__c6" (.address sender) (by decide)).withWithdrawn (withdrawn + calldataWord out 0)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
