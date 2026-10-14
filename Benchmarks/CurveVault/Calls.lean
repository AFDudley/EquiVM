import Benchmarks.CurveVault.Common
import Reasoning.VyperCalls

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: Vyper scalar returndata has exactly the scalar-word decoder,
-- without the modern tuple-size guard.
theorem decodeReturn_vyper_scalar (ty : ABIType) (out : ByteArray)
    (hty : isABIScalarWordType ty = true) :
    ABI.decodeReturnValueWithMode? .vyper ty out =
      (decodeScalarWord? ty out.toList 0).map Prod.fst := by
  have htys : [ty].all isABIScalarWordType = true := by simp [hty]
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq htys]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.vyper)
    (types := [ty]) (cursor := 0) (total := 32 * [ty].length) htys (by simp)]
  simp only [decodeScalarWordsWithMode?, decodeScalarWordWithMode_vyper_eq]
  cases h : decodeScalarWord? ty out.toList 0 with
  | none => rfl
  | some v => rcases v with ⟨value, off⟩; rfl

theorem decodeReturn_vyper_address_ok (out : ByteArray) (h32 : 32 ≤ out.size)
    (hcanon : (retWord out).toNat < EVM.addressModulus) :
    ABI.decodeReturnValueWithMode? .vyper (.elem .address) out =
      some (.address (AccountAddress.ofNat (retWord out).toNat)) := by
  have hlen : ((out.toList.drop 0).take 32).length = 32 := by
    simp only [List.drop_zero, List.length_take, byteArray_toList_eq, Array.length_toList]
    exact Nat.min_eq_left h32
  rw [decodeReturn_vyper_scalar _ _ rfl, decodeScalarWord_address_ok hlen
    (by rw [bytesToWord_take32_retWord]; exact hcanon), bytesToWord_take32_retWord]
  rfl

theorem decodeReturn_vyper_address_noncanon (out : ByteArray) (h32 : 32 ≤ out.size)
    (hcanon : ¬ (retWord out).toNat < EVM.addressModulus) :
    ABI.decodeReturnValueWithMode? .vyper (.elem .address) out = none := by
  have hlen : ((out.toList.drop 0).take 32).length = 32 := by
    simp only [List.drop_zero, List.length_take, byteArray_toList_eq, Array.length_toList]
    exact Nat.min_eq_left h32
  rw [decodeReturn_vyper_scalar _ _ rfl, decodeScalarWord_address_none_noncanon hlen
    (by rw [bytesToWord_take32_retWord]; exact hcanon)]
  rfl

theorem decodeReturn_vyper_address_short (out : ByteArray) (h32 : out.size < 32) :
    ABI.decodeReturnValueWithMode? .vyper (.elem .address) out = none := by
  have hlen : ¬ ((out.toList.drop 0).take 32).length = 32 := by
    simp only [List.drop_zero, List.length_take, byteArray_toList_eq, Array.length_toList]
    change ¬ min 32 out.size = 32
    omega
  rw [decodeReturn_vyper_scalar _ _ rfl, decodeScalarWord_address_none_short hlen]
  rfl

theorem decodeReturn_vyper_uint256_ok (out : ByteArray) (h32 : 32 ≤ out.size) :
    ABI.decodeReturnValueWithMode? .vyper (.elem (.int (.uint ⟨256, by decide⟩))) out =
      some (.int (Int.ofNat (retWord out).toNat)) := by
  have hlen : ((out.toList.drop 0).take 32).length = 32 := by
    simp only [List.drop_zero, List.length_take, byteArray_toList_eq, Array.length_toList]
    exact Nat.min_eq_left h32
  rw [decodeReturn_vyper_scalar _ _ rfl, decodeScalarWord_uint256_ok hlen,
    bytesToWord_take32_retWord]
  rfl

theorem decodeReturn_vyper_uint256_short (out : ByteArray) (h32 : out.size < 32) :
    ABI.decodeReturnValueWithMode? .vyper (.elem (.int (.uint ⟨256, by decide⟩))) out = none := by
  have hlen : ¬ ((out.toList.drop 0).take 32).length = 32 := by
    simp only [List.drop_zero, List.length_take, byteArray_toList_eq, Array.length_toList]
    change ¬ min 32 out.size = 32
    omega
  rw [decodeReturn_vyper_scalar _ _ rfl, decodeScalarWord_uint256_none_short hlen]
  rfl

-- LIBRARY CANDIDATE: Vyper emits a nullary call's selector in the final four bytes of MSTORE.
theorem vyperNullaryCallData (word : UInt256) (sel mem : ByteArray) (off : Nat)
    (hsel : word.toByteArray.extract 28 32 = sel) (hgap : off - mem.size < USize.size) :
    ABI.encodeCallWithSelector? sel [] [] =
      some ((word.toByteArray.write 0 mem off 32).readWithPadding (off + 28) 4) := by
  rw [toByteArray_write_read_window_of_gap word mem off 28 4
    (by decide +kernel) (by decide +kernel) (by decide +kernel) hgap, hsel]
  simp [ABI.encodeCallWithSelector?, ABI.encodeABIValues?, ABI.abiTupleHeadSize?,
    ABI.encodeABIValuesFrom?]

-- GENERALIZES Reasoning.VyperCalls.write_out_eq_word: directly read the bounded CALL output buffer.
theorem memLoad_callOutput32 (out mem : ByteArray) (off : Nat)
    (h32 : 32 ≤ out.size) (hwide : out.size < UInt256.size)
    (hin : off + 32 ≤ mem.size) (hoff : off < UInt256.size) (hgap : off - mem.size < USize.size) :
    memLoad (UInt256.ofNat off)
      (out.write 0 mem off (min (UInt256.ofNat 32) (UInt256.ofNat out.size)).toNat) = retWord out := by
  rw [min32_toNat _ h32 hwide, write_out_eq_word out mem off h32 hin]
  exact memLoad_write_back _ _ off hoff hgap

end Benchmarks.CurveVault
