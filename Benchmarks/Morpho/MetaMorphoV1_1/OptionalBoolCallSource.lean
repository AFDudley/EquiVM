import Benchmarks.Morpho.MetaMorphoV1_1.OptionalBoolSource
import Benchmarks.Morpho.MetaMorphoV1_1.OptionalCallSource

/-! Source body of the allocation-aware Boolean approval probe. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def optionalBoolRawFrame (imms : Store) (token : AccountAddress) (data : ByteArray)
    (ptr : UInt256) (ok : Bool) (out : ByteArray) : Frame :=
  { optionalCallFrame imms token data ptr with
    locals := ((optionalCallFrame imms token data ptr).locals.insert "success" (.bool ok)).insert
      "returndata" (.bytes out) }

def optionalBoolResultFrame (imms : Store) (token : AccountAddress) (data : ByteArray)
    (ptr : UInt256) (ok : Bool) (out : ByteArray) : Frame :=
  callReturnFrame (optionalBoolRawFrame imms token data ptr ok out) ptr out

theorem allocatedOptionalReturnBool_body : allocatedOptionalReturnBoolFunction.body =
    [.lowLevelCall (.var "token") (.intLit 0) (.var "data") "success" "returndata" true,
     reserveCallReturn, .return [optionalBoolExpr, .var cursorName]] := by
  change [_ , _] ++ allocationBody (fun _ => none) (fun _ => 0)
    [.return [optionalBoolExpr]] = _
  simp only [allocationBody, allocationStatement, returnValueExpr,
    List.nil_append, List.cons_append]

theorem optionalBoolCallPrefix {evm evm' : State} (imms : Store) (token : AccountAddress)
    (data : ByteArray) (ptr : UInt256) (ok : Bool) (out : ByteArray) {result : ExecResult}
    (hcall : callViaEVM evm token 0 data (ok, evm', out))
    (htail : ExecBlock config (optionalBoolRawFrame imms token data ptr ok out) evm'
      [reserveCallReturn, .return [optionalBoolExpr, .var cursorName]] result) :
    ExecBlock config (optionalCallFrame imms token data ptr) evm
      allocatedOptionalReturnBoolFunction.body result := by
  rw [allocatedOptionalReturnBool_body]
  apply ExecBlock.consNormal _ htail
  exact lowLevelCallSource
    (by simp only [evalExpr?, optionalCallFrame, store_get_self, EvalResult.ofOption])
    (by simp only [evalExpr?, pure])
    (by simp [evalExpr?, optionalCallFrame, Std.HashMap.getElem_insert, EvalResult.ofOption]) hcall

theorem optionalBoolRawFrame_cursor (imms : Store) (token : AccountAddress) (data : ByteArray)
    (ptr : UInt256) (ok : Bool) (out : ByteArray) :
    (optionalBoolRawFrame imms token data ptr ok out).locals.get? cursorName =
      some (uint256Value ptr) := by
  simp [optionalBoolRawFrame, optionalCallFrame, cursorName, Std.HashMap.getElem_insert]

theorem optionalBoolResultFrame_token (imms : Store) (token : AccountAddress) (data : ByteArray)
    (ptr : UInt256) (ok : Bool) (out : ByteArray) :
    (optionalBoolResultFrame imms token data ptr ok out).locals.get? "token" =
      some (.address token) := by
  rw [optionalBoolResultFrame, callReturnFrame_get _ _ _ _ (by decide)]
  simp [optionalBoolRawFrame, optionalCallFrame, Std.HashMap.getElem_insert]

theorem optionalBoolResultFrame_success (imms : Store) (token : AccountAddress) (data : ByteArray)
    (ptr : UInt256) (ok : Bool) (out : ByteArray) :
    (optionalBoolResultFrame imms token data ptr ok out).locals.get? "success" = some (.bool ok) := by
  rw [optionalBoolResultFrame, callReturnFrame_get _ _ _ _ (by decide)]
  simp [optionalBoolRawFrame, Std.HashMap.getElem_insert]

theorem optionalBoolResultFrame_data (imms : Store) (token : AccountAddress) (data : ByteArray)
    (ptr : UInt256) (ok : Bool) (out : ByteArray) :
    (optionalBoolResultFrame imms token data ptr ok out).locals.get? "returndata" = some (.bytes out) := by
  rw [optionalBoolResultFrame, callReturnFrame_get _ _ _ _ (by decide)]
  exact store_get_self _ _ _

theorem optionalBoolCallBodyReturns {evm evm' : State} (imms : Store) (token : AccountAddress)
    (data : ByteArray) (ptr : UInt256) (ok : Bool) (out : ByteArray)
    (hcall : callViaEVM evm token 0 data (ok, evm', out))
    (hfit : callReturnFits ptr out) (hvalid : optionalBoolDecodable ok out) :
    ExecFuncBody config (optionalCallFrame imms token data ptr) evm
      allocatedOptionalReturnBoolFunction.body
      (.returned (optionalBoolResultFrame imms token data ptr ok out) evm'
        (some [.bool (optionalBoolValue evm'.accountMap (UInt256.ofNat token.toNat) ok out),
          uint256Value (callReturnCursor ptr out)])) := by
  apply ExecFuncBody.execBlockRet
  apply optionalBoolCallPrefix imms token data ptr ok out hcall
  apply ExecBlock.consNormal (reserveCallReturnReturns allocateFunction_lookup
    (optionalBoolRawFrame_cursor ..) (store_get_self _ _ _) hfit)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  have hout : out.size < 2 ^ 255 := by rcases hfit with hz | ⟨hs, _⟩ <;> omega
  have he := optionalBoolSource (evm := evm') (optionalBoolResultFrame_token imms token data ptr ok out)
    (optionalBoolResultFrame_success ..) (optionalBoolResultFrame_data ..) hout hvalid
  have hc := callReturnFrame_cursor _ _ out (optionalBoolRawFrame_cursor imms token data ptr ok out)
  change (optionalBoolResultFrame imms token data ptr ok out).locals.get? cursorName = _ at hc
  change evalExprs? config (optionalBoolResultFrame imms token data ptr ok out) evm' _ = _
  simp only [evalExprs?, he, evalExpr?, hc,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem optionalBoolCallBodyReverts {evm evm' : State} (imms : Store) (token : AccountAddress)
    (data : ByteArray) (ptr : UInt256) (ok : Bool) (out : ByteArray)
    (hcall : callViaEVM evm token 0 data (ok, evm', out))
    (hbad : ¬ callReturnFits ptr out ∨ ¬ optionalBoolDecodable ok out) :
    ExecFuncBody config (optionalCallFrame imms token data ptr) evm
      allocatedOptionalReturnBoolFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply optionalBoolCallPrefix imms token data ptr ok out hcall
  by_cases hfit : callReturnFits ptr out
  · apply ExecBlock.consNormal (reserveCallReturnReturns allocateFunction_lookup
      (optionalBoolRawFrame_cursor ..) (store_get_self _ _ _) hfit)
    have hv := hbad.resolve_left (not_not_intro hfit)
    have hok : ok = true := by cases ok <;> simp_all [optionalBoolDecodable]
    subst ok
    have hout : out.size < 2 ^ 255 := by rcases hfit with hz | ⟨hs, _⟩ <;> omega
    have he := optionalBoolSourceReverts (evm := evm') (optionalBoolResultFrame_success imms token data ptr true out)
      (optionalBoolResultFrame_data ..) hout hv
    apply ExecBlock.consRevert (ExecStmt.returnRevert ?_)
    change evalExprs? config (optionalBoolResultFrame imms token data ptr true out) evm' _ = _
    simp only [evalExprs?, he, bind, EvalResult.bind]
  · exact ExecBlock.consRevert (reserveCallReturnReverts allocateFunction_lookup
      (optionalBoolRawFrame_cursor ..) (store_get_self _ _ _) hfit)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
