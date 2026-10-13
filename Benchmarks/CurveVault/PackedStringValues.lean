import Benchmarks.CurveVault.InitializeSymbolMemory
import Benchmarks.CurveVault.SymbolReturnABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

-- GENERALIZES Reasoning.ABI.encodePacked_uint256 — parameterize the integer width.
theorem encodePacked_uint_word (width : ABI.BitWidth) (w : UInt256)
    (hwidth : width.val ≠ 0) (hfit : w.toNat < EVM.twoPow width.val) :
    encodePackedValue? (.elem (.int (.uint width))) (.int (Int.ofNat w.toNat)) =
      some (w.toByteArray.toList.drop (32 - width.val / 8)) := by
  have hword : EVM.word w.toNat = w := u256_ofNat_toNat w
  simp [encodePackedValue?, encodeABIWord?, hword, hfit, hwidth, word_toBytesBE_eq_toByteArray_toList]

theorem encodePacked_uint128_tail (size : UInt256) (hsize : size.toNat ≤ 32) :
    encodePackedValue? (.elem (.int (.uint ⟨128, by decide⟩))) (.int (Int.ofNat size.toNat)) =
      some (size.toByteArray.extract 16 32).toList := by
  rw [encodePacked_uint_word _ _ (by decide) (by change size.toNat < 2 ^ 128; omega), extract_toList]
  congr 1
  change size.toByteArray.toList.drop 16 = (size.toByteArray.toList.drop 16).take 16
  symm
  apply List.take_of_length_le
  simp only [List.length_drop, byteArray_toList_eq, Array.length_toList]
  change size.toByteArray.size - 16 ≤ 16
  rw [toByteArray_size]

-- LIBRARY CANDIDATE: turn packed argument bytes into an evaluated byte-array value.
theorem evalExpr_packed_bytes {cfg : Config} {frame : Frame} {evm : State}
    {args : List (ABIType × Expr)} {data : ByteArray}
    (h : evalPackedArgs? cfg frame evm args = .ok data.toList) :
    evalExpr? cfg frame evm (.abiEncodePacked args) = .ok (.bytes data) := by
  rw [evalExpr?, h]
  simp only [EvalResult.bind, bind, pure, byteArray_mk_toList_toArray]

theorem vaultNameData_size (size word : UInt256) : (vaultNameData size word).size = 64 := by
  simp only [vaultNameData, ByteArray.size_append, ByteArray.size_extract, toByteArray_size]
  rfl

theorem vaultSymbolData_size (size word : UInt256) : (vaultSymbolData size word).size = 64 := by
  simp only [vaultSymbolData, ByteArray.size_append, ByteArray.size_extract, toByteArray_size]
  rfl

theorem vaultNamePrefix_bytes : "Curve Vault for ".toUTF8 = vaultNamePrefix.toByteArray.extract 0 16 := by
  native_decide

theorem vaultSymbolPrefix_bytes : "cv".toUTF8 = vaultSymbolPrefix.toByteArray.extract 0 2 := by
  native_decide

theorem vaultEncodeSymbol (evm : State) (locals : Store) (word : UInt256)
    (hw : locals.get? "symbol_word" = some (.fixedBytes ⟨31, by decide⟩ word.toByteArray.toList)) :
    evalExpr? config {contract := contract, locals := locals} evm
      (.abiEncodePacked [(.elem (.bytes ⟨31, by decide⟩), .var "symbol_word")]) = .ok (.bytes word.toByteArray) := by
  apply evalExpr_packed_bytes
  apply evalPackedArgs_single (v := .fixedBytes ⟨31, by decide⟩ word.toByteArray.toList)
    (by simp only [evalExpr?, hw, EvalResult.ofOption])
  simpa only [wordBytes32Value, word_toBytesBE_eq_toByteArray_toList] using encodePacked_bytes32 word

theorem vaultEncodedSymbolSlice (evm : State) (locals : Store) (word : UInt256)
    (he : locals.get? "encoded_symbol" = some (.bytes word.toByteArray)) :
    evalExpr? config {contract := contract, locals := locals} evm
      (.bytesSlice (.var "encoded_symbol") (.intLit 18) (.intLit 32)) =
      .ok (.bytes (word.toByteArray.extract 18 32)) := by
  simp only [evalExpr?, he, EvalResult.ofOption, EvalResult.bind, bind, pure]
  simp [sliceBytes?, toByteArray_size]

end Benchmarks.CurveVault
