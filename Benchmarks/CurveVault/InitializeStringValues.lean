import Benchmarks.CurveVault.PackedStringValues

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultStringPackedArgs (isName : Bool) : List (ABIType × Expr) :=
  [(.string, .bytesLit (if isName then "Curve Vault for ".toUTF8 else "cv".toUTF8)),
    (.elem (.bytes ⟨31, by decide⟩), .var "symbol_word")] ++
  (if isName then [] else [(.bytes, .bytesSlice (.var "encoded_symbol") (.intLit 18) (.intLit 32))]) ++
  [(.elem (.int (.uint ⟨128, by decide⟩)), .var "symbol_size")]

def vaultStringTupleExpr (isName : Bool) : Expr :=
  .tupleLit [.binary .add (.var "symbol_size") (.intLit (if isName then 16 else 2)),
    .abiEncodePacked (vaultStringPackedArgs isName)]

theorem vaultStringPackedEval (isName : Bool) (evm : State) (locals : Store) (size word : UInt256)
    (hn : locals.get? "symbol_size" = some (.int (Int.ofNat size.toNat)))
    (hw : locals.get? "symbol_word" = some (.fixedBytes ⟨31, by decide⟩ word.toByteArray.toList))
    (he : locals.get? "encoded_symbol" = some (.bytes word.toByteArray)) (hsize : size.toNat ≤ 32) :
    evalExpr? config {contract := contract, locals := locals} evm
      (.abiEncodePacked (vaultStringPackedArgs isName)) =
      .ok (.bytes (if isName then vaultNameData size word else vaultSymbolData size word)) := by
  have hn' : evalExpr? config {contract := contract, locals := locals} evm (.var "symbol_size") =
      .ok (.int (Int.ofNat size.toNat)) := by simp only [evalExpr?, hn, EvalResult.ofOption]
  have hw' : evalExpr? config {contract := contract, locals := locals} evm (.var "symbol_word") =
      .ok (.fixedBytes ⟨31, by decide⟩ word.toByteArray.toList) := by simp only [evalExpr?, hw, EvalResult.ofOption]
  have hwe : encodePackedValue? (.elem (.bytes ⟨31, by decide⟩))
      (.fixedBytes ⟨31, by decide⟩ word.toByteArray.toList) = some word.toByteArray.toList := by
    simpa only [wordBytes32Value, word_toBytesBE_eq_toByteArray_toList] using encodePacked_bytes32 word
  have hend := evalPackedArgs_single hn' (encodePacked_uint128_tail size hsize)
  apply evalExpr_packed_bytes
  cases isName
  · have hs := evalPackedArgs_cons (ty := .bytes) (vaultEncodedSymbolSlice evm locals word he) rfl hend
    have hm := evalPackedArgs_cons hw' hwe hs
    have hp := evalPackedArgs_cons
      (show evalExpr? config {contract := contract, locals := locals} evm (.bytesLit "cv".toUTF8) =
        .ok (.bytes "cv".toUTF8) from by rw [evalExpr?]; rfl)
      (show encodePackedValue? .string (.bytes "cv".toUTF8) = some "cv".toUTF8.toList from rfl) hm
    change evalPackedArgs? config {contract := contract, locals := locals} evm
      [(.string, .bytesLit "cv".toUTF8), (.elem (.bytes ⟨31, by decide⟩), .var "symbol_word"),
        (.bytes, .bytesSlice (.var "encoded_symbol") (.intLit 18) (.intLit 32)),
        (.elem (.int (.uint ⟨128, by decide⟩)), .var "symbol_size")] = .ok (vaultSymbolData size word).toList
    simpa only [vaultSymbolData, byteArray_toList_append, ← vaultSymbolPrefix_bytes, List.append_assoc] using hp
  · have hm := evalPackedArgs_cons hw' hwe hend
    have hp := evalPackedArgs_cons
      (show evalExpr? config {contract := contract, locals := locals} evm (.bytesLit "Curve Vault for ".toUTF8) =
        .ok (.bytes "Curve Vault for ".toUTF8) from by rw [evalExpr?]; rfl)
      (show encodePackedValue? .string (.bytes "Curve Vault for ".toUTF8) = some "Curve Vault for ".toUTF8.toList from rfl) hm
    change evalPackedArgs? config {contract := contract, locals := locals} evm
      [(.string, .bytesLit "Curve Vault for ".toUTF8), (.elem (.bytes ⟨31, by decide⟩), .var "symbol_word"),
        (.elem (.int (.uint ⟨128, by decide⟩)), .var "symbol_size")] = .ok (vaultNameData size word).toList
    simpa only [vaultNameData, byteArray_toList_append, ← vaultNamePrefix_bytes, List.append_assoc] using hp

theorem vaultStringTupleEval (isName : Bool) (evm : State) (locals : Store) (size word : UInt256)
    (hn : locals.get? "symbol_size" = some (.int (Int.ofNat size.toNat)))
    (hw : locals.get? "symbol_word" = some (.fixedBytes ⟨31, by decide⟩ word.toByteArray.toList))
    (he : locals.get? "encoded_symbol" = some (.bytes word.toByteArray)) (hsize : size.toNat ≤ 32) :
    evalExpr? config {contract := contract, locals := locals} evm (vaultStringTupleExpr isName) =
      .ok (.tuple [.int (Int.ofNat (size.toNat + if isName then 16 else 2)),
        .bytes (if isName then vaultNameData size word else vaultSymbolData size word)]) := by
  have hp := vaultStringPackedEval isName evm locals size word hn hw he hsize
  have hn' : evalExpr? config {contract := contract, locals := locals} evm
      (.binary .add (.var "symbol_size") (.intLit (if isName then 16 else 2))) =
      .ok (.int (Int.ofNat (size.toNat + if isName then 16 else 2))) := by
    simp only [evalExpr?, hn, EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?]
    cases isName <;> rfl
  rw [vaultStringTupleExpr, evalExpr?, evalExprList?, hn']
  simp only [evalExprList?, hp, EvalResult.bind, bind, pure]

end Benchmarks.CurveVault
