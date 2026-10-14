import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDecimalsResult
import Benchmarks.Morpho.MetaMorphoV1_1.CallReturnSource
import Benchmarks.Morpho.MetaMorphoV1_1.Uint128Cast
import Reasoning.ABIComposite

/-! Source evaluation of the optional uint8-valued decimals response. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def constructorDecimalsValue (ok : Bool) (out : ByteArray) : Value :=
  .tuple [.bool (decide (constructorDecimalsValid ok out)), uint256Value (constructorDecimalsWord ok out)]

def constructorDecimalsGuard : Expr :=
  .binary .and (.var "success")
    (.binary .ge (.arrayLength .localVar ⟨"encodedDecimals", []⟩) (.intLit 32))

def constructorDecimalsReturnTail : List Stmt :=
  [.ite constructorDecimalsGuard
    [.letDecl "returnedDecimals" (some abiUInt256) (.abiDecode abiUInt256 (.var "encodedDecimals")),
     .ite (.binary .le (.var "returnedDecimals") (.intLit 255))
       [.return [.tupleLit [.boolLit true,
         .cast (.var "returnedDecimals") (.elem (.int (.uint ⟨8, by decide⟩)))], .var cursorName]] []] [],
   .return [.tupleLit [.boolLit false, .intLit 0], .var cursorName]]

set_option maxRecDepth 2000 in
theorem allocatedTryGetAssetDecimals_body : allocatedTryGetAssetDecimalsFunction.body =
    [reserveBytes 36,
     .lowLevelCall (.var "asset_") (.intLit 0) (.abiEncodeCall "decimals" [])
       "success" "encodedDecimals" false,
     .letDecl "returndata" none (.var "encodedDecimals"), reserveCallReturn] ++
      constructorDecimalsReturnTail := by
  change _ ++ allocationBody (fun _ => none) (fun _ => 0)
    [.ite constructorDecimalsGuard
      [.letDecl "returnedDecimals" (some abiUInt256) (.abiDecode abiUInt256 (.var "encodedDecimals")),
       .ite (.binary .le (.var "returnedDecimals") (.intLit 255))
         [.return [.boolLit true,
           .cast (.var "returnedDecimals") (.elem (.int (.uint ⟨8, by decide⟩)))]] []] [],
     .return [.boolLit false, .intLit 0]] = _
  simp only [allocationBody, allocationStatement, returnValueExpr, constructorDecimalsReturnTail,
    List.nil_append, List.cons_append]
  rfl

-- LIBRARY CANDIDATE: a complete modern ABI uint256 return decodes to its first EVM word.
theorem returnUint256Source {frame : Frame} {evm : State} {out : ByteArray} {name : Ident}
    (hget : frame.locals.get? name = some (.bytes out))
    (hlen : 32 ≤ out.size) (hsize : out.size < 2 ^ 255) :
    evalExpr? config frame evm (.abiDecode abiUInt256 (.var name)) =
      .ok (uint256Value (calldataWord out 0)) := by
  have hword := decode_word_at_eq out 0 (by omega) (by decide)
  simp only [List.drop_zero] at hword
  have h32 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, byteArray_toList_eq, Array.length_toList]
    change min 32 out.size = 32
    omega
  have hd : decodeReturnValue? abiUInt256 out = some (uint256Value (calldataWord out 0)) := by
    unfold decodeReturnValue?
    rw [decodeReturnValues_scalarWords_eq (by decide), if_neg (by
      simp only [List.isEmpty_cons, byteArray_toList_eq, Array.length_toList]
      exact fun h => Nat.not_le_of_lt hsize h.2)]
    simp only [decodeScalarWords_uint256_ok (by simpa only [List.drop_zero] using h32),
      hword]
  simp only [evalExpr?, hget, EvalResult.ofOption, bind, EvalResult.bind]
  change (match decodeReturnValue? abiUInt256 out with
    | some value => EvalResult.ok value | none => EvalResult.revert) = _
  rw [hd]

theorem constructorDecimalsGuardSource {frame : Frame} {evm : State} {ok : Bool} {out : ByteArray}
    (hok : frame.locals.get? "success" = some (.bool ok))
    (hout : frame.locals.get? "encodedDecimals" = some (.bytes out)) :
    evalExpr? config frame evm constructorDecimalsGuard =
      .ok (.bool (decide (ok = true ∧ 32 ≤ out.size))) := by
  have hlen : evalExpr? config frame evm
      (.arrayLength .localVar ⟨"encodedDecimals", []⟩) = .ok (.int (Int.ofNat out.size)) := by
    simp only [evalExpr?, hout, readLocalPath?, bind, EvalResult.bind, pure]
  have ht := boolAndSource
    (show evalExpr? config frame evm (.var "success") = .ok (.bool ok) by
      simp only [evalExpr?, hok, EvalResult.ofOption])
    (naturalGeSource hlen (show evalExpr? config frame evm (.intLit 32) =
      .ok (.int (Int.ofNat 32)) by simp only [evalExpr?, pure]; rfl))
  cases ok <;> simpa [constructorDecimalsGuard] using ht

theorem constructorDecimalsTailSource {frame : Frame} {evm : State} {ok : Bool}
    {out : ByteArray} {ptr : UInt256}
    (hok : frame.locals.get? "success" = some (.bool ok))
    (hout : frame.locals.get? "encodedDecimals" = some (.bytes out))
    (hptr : frame.locals.get? cursorName = some (uint256Value ptr))
    (hsize : out.size < 2 ^ 255) :
    ∃ frame', ExecBlock config frame evm constructorDecimalsReturnTail
      (.returned frame' evm (some [constructorDecimalsValue ok out, uint256Value ptr])) := by
  have hc := constructorDecimalsGuardSource (evm := evm) hok hout
  by_cases hready : ok = true ∧ 32 ≤ out.size
  · let decoded := { frame with
        locals := frame.locals.insert "returnedDecimals" (uint256Value (calldataWord out 0)) }
    have hd := returnUint256Source (evm := evm) hout hready.2 hsize
    have hx : evalExpr? config decoded evm (.var "returnedDecimals") =
        .ok (uint256Value (calldataWord out 0)) := by
      simp only [evalExpr?, decoded, store_get_self, EvalResult.ofOption]
    have hp : decoded.locals.get? cursorName = some (uint256Value ptr) := by
      rw [show decoded.locals = frame.locals.insert "returnedDecimals"
        (uint256Value (calldataWord out 0)) from rfl,
        store_get_ne _ _ (show ("returnedDecimals" == cursorName) = false by decide), hptr]
    have hv := naturalLeSource hx (show evalExpr? config decoded evm (.intLit 255) =
      .ok (.int (Int.ofNat 255)) by simp only [evalExpr?, pure]; rfl)
    by_cases hfit : (calldataWord out 0).toNat ≤ 255
    · have hgood : constructorDecimalsValid ok out := ⟨hready.1, hready.2, hfit⟩
      refine ⟨decoded, ?_⟩
      apply ExecBlock.consReturn (ExecStmt.iteTrue (by simpa only [hready, decide_true] using hc) ?_)
      apply ExecBlock.consNormal (ExecStmt.letDecl hd)
      apply ExecBlock.consReturn (ExecStmt.iteTrue (by simpa only [hfit, decide_true] using hv) ?_)
      apply ExecBlock.consReturn (ExecStmt.return ?_)
      have hcast := uintCastSource ⟨8, by decide⟩ hx (by change _ < 256; omega)
      change evalExprs? config decoded evm _ = _
      simp only [constructorDecimalsValue, constructorDecimalsWord, hgood, decide_true,
        if_true, evalExprs?, evalExprList?, hcast, evalExpr?, hp, EvalResult.ofOption,
        bind, EvalResult.bind, pure]
    · have hbad : ¬ constructorDecimalsValid ok out := fun h => hfit h.2.2
      refine ⟨decoded, ?_⟩
      apply ExecBlock.consNormal (ExecStmt.iteTrue (by simpa only [hready, decide_true] using hc) ?_)
      · apply ExecBlock.consReturn (ExecStmt.return ?_)
        change evalExprs? config decoded evm _ = _
        simp only [constructorDecimalsValue, constructorDecimalsWord, hbad, decide_false,
          if_false, evalExprs?, evalExprList?, evalExpr?, hp, EvalResult.ofOption,
          bind, EvalResult.bind, pure]
        rfl
      · exact ExecBlock.consNormal (ExecStmt.letDecl hd)
          (ExecBlock.consNormal (ExecStmt.iteFalse (by simpa only [hfit, decide_false] using hv)
            ExecBlock.nil) ExecBlock.nil)
  · have hbad : ¬ constructorDecimalsValid ok out := fun h => hready ⟨h.1, h.2.1⟩
    refine ⟨frame, ?_⟩
    apply ExecBlock.consNormal (ExecStmt.iteFalse (by simpa only [hready, decide_false] using hc) ExecBlock.nil)
    apply ExecBlock.consReturn (ExecStmt.return ?_)
    simp only [constructorDecimalsValue, constructorDecimalsWord, hbad, decide_false,
      if_false, evalExprs?, evalExprList?, evalExpr?, hptr, EvalResult.ofOption,
      bind, EvalResult.bind, pure]
    rfl

end Benchmarks.Morpho.MetaMorphoV1_1
