import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateCallSource
import Benchmarks.Morpho.MetaMorphoV1_1.ApprovalCalls

/-! Decode supplied shares, emit the supply event, and check the running supplied total. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
attribute [local irreducible] contract

def reallocateSupplyEventFrame (frame : Frame) (out : ByteArray) (sender : AccountAddress) : Frame :=
  { frame with locals := ((frame.locals.insert "suppliedShares"
      (uint256Value (calldataWord out 32))).insert "__c10" (.address sender)) }

def reallocateSupplyFinishFrame (frame : Frame) (out : ByteArray)
    (sender : AccountAddress) (total amount : UInt256) : Frame :=
  { frame with locals := ((reallocateSupplyEventFrame frame out sender).locals.insert
      "totalSupplied" (uint256Value (total + amount))) }

set_option maxRecDepth 2000 in
theorem reallocateSupplyEventPrefix {frame : Frame} {evm : State} {out : ByteArray}
    (hc : frame.contract = contract)
    (hret : frame.locals.get? "__c9" = some (strictPairCallValue out)) :
    ABlock config evm frame (reallocateSupplyBody.drop 8)
      (reallocateSupplyEventFrame frame out evm.executionEnv.source) (reallocateSupplyBody.drop 10) := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hc
  subst c
  constructor
  intro result htail
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value (calldataWord out 32)) ?_) ?_
  · simp only [evalExpr?, hret, EvalResult.ofOption, strictPairCallValue, bind, EvalResult.bind,
      tupleGetValue?, List.getElem?_cons_zero, List.getElem?_cons_succ]
  exact ExecBlock.consNormal (msgSenderCall _ _ evm "__c10") htail

theorem reallocateSupplyEventFrame_preserves (frame : Frame) (out : ByteArray) (sender : AccountAddress)
    (name : Ident) (hc : ("__c10" == name) = false) (hs : ("suppliedShares" == name) = false) :
    (reallocateSupplyEventFrame frame out sender).locals.get? name = frame.locals.get? name := by
  rw [reallocateSupplyEventFrame, store_get_ne _ _ hc, store_get_ne _ _ hs]

theorem reallocateSupplyEventArgs {frame : Frame} {evm : State} {id amount : UInt256} (out : ByteArray)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (ha : frame.locals.get? "suppliedAssets" = some (uint256Value amount)) :
    evalExprs? config (reallocateSupplyEventFrame frame out evm.executionEnv.source) evm
      [.var "__c10", .var "id", .var "suppliedAssets", .var "suppliedShares"] =
      .ok [.address evm.executionEnv.source, wordBytes32Value id,
        uint256Value amount, uint256Value (calldataWord out 32)] := by
  simp only [evalExprs?, evalExpr?, reallocateSupplyEventFrame, store_get_self,
    store_get_ne _ _ (by decide : ("__c10" == "id") = false),
    store_get_ne _ _ (by decide : ("suppliedShares" == "id") = false),
    store_get_ne _ _ (by decide : ("__c10" == "suppliedAssets") = false),
    store_get_ne _ _ (by decide : ("__c10" == "suppliedShares") = false),
    store_get_ne _ _ (by decide : ("suppliedShares" == "suppliedAssets") = false),
    hid, ha, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem reallocateSupplyFinishSource {frame : Frame} {evm : State} {out : ByteArray} {total id amount : UInt256}
    (hc : frame.contract = contract)
    (hret : frame.locals.get? "__c9" = some (strictPairCallValue out))
    (ht : frame.locals.get? "totalSupplied" = some (uint256Value total))
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (ha : frame.locals.get? "suppliedAssets" = some (uint256Value amount))
    (hfit : total.toNat + amount.toNat < UInt256.size) :
    ExecBlock config frame evm (reallocateSupplyBody.drop 8)
      (.ok (reallocateSupplyFinishFrame frame out evm.executionEnv.source total amount) evm) := by
  have htotal : (reallocateSupplyEventFrame frame out evm.executionEnv.source).locals.get? "totalSupplied" =
      some (uint256Value total) := by
    rw [reallocateSupplyEventFrame_preserves _ _ _ _ (by decide) (by decide)]; exact ht
  have hamount : (reallocateSupplyEventFrame frame out evm.executionEnv.source).locals.get? "suppliedAssets" =
      some (uint256Value amount) := by
    rw [reallocateSupplyEventFrame_preserves _ _ _ _ (by decide) (by decide)]; exact ha
  apply (reallocateSupplyEventPrefix hc hret).run
  refine ExecBlock.consNormal (ExecStmt.emit (reallocateSupplyEventArgs out hid ha)) ?_
  exact ExecBlock.consNormal (ExecStmt.assign
    (checkedAddSourceOk (evalLocalValue htotal) (evalLocalValue hamount) hfit)
    (assignLocalValue htotal)) ExecBlock.nil

theorem reallocateSupplyFinishRevert {frame : Frame} {evm : State} {out : ByteArray} {total id amount : UInt256}
    (hc : frame.contract = contract)
    (hret : frame.locals.get? "__c9" = some (strictPairCallValue out))
    (ht : frame.locals.get? "totalSupplied" = some (uint256Value total))
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (ha : frame.locals.get? "suppliedAssets" = some (uint256Value amount))
    (hbad : UInt256.size ≤ total.toNat + amount.toNat) :
    ExecBlock config frame evm (reallocateSupplyBody.drop 8) .reverted := by
  have htotal : (reallocateSupplyEventFrame frame out evm.executionEnv.source).locals.get? "totalSupplied" =
      some (uint256Value total) := by
    rw [reallocateSupplyEventFrame_preserves _ _ _ _ (by decide) (by decide)]; exact ht
  have hamount : (reallocateSupplyEventFrame frame out evm.executionEnv.source).locals.get? "suppliedAssets" =
      some (uint256Value amount) := by
    rw [reallocateSupplyEventFrame_preserves _ _ _ _ (by decide) (by decide)]; exact ha
  apply (reallocateSupplyEventPrefix hc hret).run
  refine ExecBlock.consNormal (ExecStmt.emit (reallocateSupplyEventArgs out hid ha)) ?_
  exact ExecBlock.consRevert (ExecStmt.assignExprRevert
    (checkedAddSourceOverflow (evalLocalValue htotal) (evalLocalValue hamount) hbad))

theorem reallocateSupplyFinishStatic {frame : Frame} {evm : State} {out : ByteArray} {id amount : UInt256}
    (hc : frame.contract = contract)
    (hret : frame.locals.get? "__c9" = some (strictPairCallValue out))
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (ha : frame.locals.get? "suppliedAssets" = some (uint256Value amount))
    (hperm : evm.executionEnv.perm = false) :
    ExecBlock config frame evm (reallocateSupplyBody.drop 8) .staticViolation := by
  apply (reallocateSupplyEventPrefix hc hret).run
  exact ExecBlock.consStatic (ExecStmt.emitStatic (reallocateSupplyEventArgs out hid ha) hperm)

theorem ReallocateLocals.supplyFinish {v : MetaMorphoV1_1Immutables} {frame : Frame} {values : List Value}
    {i supplied withdrawn cursor : UInt256} (h : ReallocateLocals v frame values i supplied withdrawn cursor)
    (out : ByteArray) (sender : AccountAddress) (amount : UInt256) :
    ReallocateLocals v (reallocateSupplyFinishFrame frame out sender supplied amount) values i
      (supplied + amount) withdrawn cursor :=
  ((h.insert "suppliedShares" (uint256Value (calldataWord out 32)) (by decide)).insert
    "__c10" (.address sender) (by decide)).withSupplied (supplied + amount)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
