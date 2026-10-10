import Benchmarks.EAS.EAS.BuildDomain
import Benchmarks.EAS.EAS.ArrayEncoding
import Benchmarks.EAS.EAS.WordSequence
import Benchmarks.EAS.EAS.ReturnDecode
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: the bytes32-to-uint256 cast preserves the complete word.
theorem evalBytes32AsUint256 {cfg : Config} {frame : Frame} {evm : EVM.State} {e : Expr} {w : UInt256}
    (he : evalExpr? cfg frame evm e = .ok (wordBytes32Value w)) :
    evalExpr? cfg frame evm (.cast e (.elem (.int (.uint ⟨256,by decide⟩)))) =
      .ok (.int (Int.ofNat w.toNat)) := by
  simp only [evalExpr?,he,EvalResult.bind,bind,castValue?,wordBytes32Value,abiBytes32Width,
    fixedBytesToNat?,fixedBytesValid,fixedBytesSize,word_toBytesBE_length_32,fromBytesBE_word]
  rfl

-- LIBRARY CANDIDATE: decode a canonical address word under any solc 0.8 calldata plan table.
theorem decodeReturnSolc08Address_word (table : List (Nat × List ABI.CalldataPlan)) (a : AccountAddress) :
    ABI.decodeReturnValueWithMode? (.solc08Calldata table) (.elem .address)
      (UInt256.ofNat a.val).toByteArray = some (.address a) := by
  have haddr : (UInt256.ofNat a.val).toNat = a.val := addressWord_toNat_val a
  rw [decodeReturnSolc08Scalar_eq table .address _ (by decide) (by rw [toByteArray_size]; decide)]
  unfold ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (by decide)]
  have hl : (UInt256.ofNat a.val).toByteArray.toList.length = 32 := by
    rw [byteArray_toList_eq,Array.length_toList]
    exact toByteArray_size _
  rw [if_neg (by rw [hl]; decide)]
  have hw : ABI.bytesToWord ((UInt256.ofNat a.val).toByteArray.toList.drop 0 |>.take 32) = UInt256.ofNat a.val := by
    simp only [toByteArray_eq_toBytesBE,byteArray_toList_eq,List.toList_toArray,List.drop_zero,
      List.take_of_length_le (word_toBytesBE_length_32 _).le,bytesToWord_toBytesBE]
  rw [decodeScalarWords?,decodeScalarWord_address_ok (by simp only [List.drop_zero,List.length_take,hl]; rfl)
    (by rw [hw,haddr]; exact a.isLt)]
  simp only [decodeScalarWords?,bind,Option.bind,hw]
  have ha : AccountAddress.ofNat (UInt256.ofNat a.val).toNat = a := by
    rw [haddr]
    apply Fin.ext
    exact Nat.mod_eq_of_lt a.isLt
  rw [ha]

def ecdsaHalfOrder : Nat := 57896044618658097711785492504343953926418782139537452191302581570759080747168

def tryRecoverGuard : Expr := .binary .gt (.cast (.var "s") (.elem (.int (.uint ⟨256,by decide⟩))))
  (.intLit (Int.ofNat ecdsaHalfOrder))
def tryRecoverPayload (hash v r s : UInt256) : ByteArray := wordBytes [hash,v,r,s]
def tryRecoverPayloadExpr : Expr := .abiEncodePacked [
  (abiBytes32,.var "hash"),(abiUInt256,.var "v"),(abiBytes32,.var "r"),(abiBytes32,.var "s")]

theorem tryRecoverGuard_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {s : UInt256}
    (hs : frame.locals.get? "s" = some (wordBytes32Value s)) :
    evalExpr? cfg frame evm tryRecoverGuard = .ok (.bool (decide (ecdsaHalfOrder < s.toNat))) := by
  have he := evalBytes32AsUint256 (cfg := cfg) (frame := frame) (evm := evm) (e := .var "s") (w := s)
    (by simp only [evalExpr?,hs,EvalResult.ofOption])
  simp only [tryRecoverGuard,evalExpr?,he,pure,EvalResult.bind,bind,evalBinaryOp?,Int.ofNat_eq_natCast,Nat.cast_lt]

theorem tryRecoverPayload_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {hash v r s : UInt256}
    (hh : frame.locals.get? "hash" = some (wordBytes32Value hash))
    (hv : frame.locals.get? "v" = some (.int (Int.ofNat v.toNat)))
    (hr : frame.locals.get? "r" = some (wordBytes32Value r))
    (hs : frame.locals.get? "s" = some (wordBytes32Value s)) :
    evalExpr? cfg frame evm tryRecoverPayloadExpr = .ok (.bytes (tryRecoverPayload hash v r s)) := by
  apply evalPackedBytes
  simp only [tryRecoverPayload,wordBytes_eq_list,byteArray_toList_eq,List.toList_data_toByteArray,
    List.flatMap_cons,List.flatMap_nil,List.append_nil]
  apply evalPackedArgs_cons (by simp only [evalExpr?,hh,EvalResult.ofOption]) (encodePacked_bytes32 _)
  apply evalPackedArgs_cons (by simp only [evalExpr?,hv,EvalResult.ofOption]) (encodePacked_uint256 _)
  apply evalPackedArgs_cons (by simp only [evalExpr?,hr,EvalResult.ofOption]) (encodePacked_bytes32 _)
  exact evalPackedArgs_single (by simp only [evalExpr?,hs,EvalResult.ofOption]) (encodePacked_bytes32 _)

end Benchmarks.EAS.EAS
