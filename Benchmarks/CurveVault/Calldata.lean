import Benchmarks.CurveVault.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

-- GENERALIZES Reasoning.Theory.decodeCalldata_uint256_ok to Vyper's decoder,
-- which accepts arbitrary suffixes without a signed-length restriction.
theorem decodeCalldataWithMode_vyper_uint256_ok {cd : ByteArray} {x : Solm.Ident}
    (hsz : 36 ≤ cd.size) :
    decodeCalldataWithMode .vyper [x] [abiUInt256] cd =
      some ((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  rw [decodeCalldataWithMode_vyperScalarWords_eq (by decide),
    if_neg (by rw [htlen]; omega), decodeScalarWords_uint256_ok htake]
  change decodeCalldata.insertValues [x]
    [.int (Int.ofNat (ABI.bytesToWord ((cd.toList.drop 4).take 32)).toNat)] ∅ = _
  rw [decode_word_at_eq cd 4 (by omega) (by norm_num)]
  rfl

-- GENERALIZES Reasoning.Theory.decodeCalldata_uint256_none_short to Vyper.
theorem decodeCalldataWithMode_vyper_uint256_none_short {cd : ByteArray} {x : Solm.Ident}
    (hshort : cd.size < 36) : decodeCalldataWithMode .vyper [x] [abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldataWithMode_vyperScalarWords_eq (by decide)]
  by_cases hsz : cd.size < 4
  · rw [if_pos (by rw [htlen]; omega)]
  · rw [if_neg (by rw [htlen]; omega), decodeScalarWords_uint256_none_short
      (by rw [List.length_drop, htlen]; omega)]

-- LIBRARY CANDIDATE: Vyper's scalar Boolean calldata accepts exactly zero or one.
theorem decodeCalldataWithMode_vyper_bool_ok {cd : ByteArray} {x : Solm.Ident} {b : Bool}
    (hsz : 36 ≤ cd.size) (hword : calldataWord cd 4 = if b then ⟨1⟩ else ⟨0⟩) :
    decodeCalldataWithMode .vyper [x] [.elem .bool] cd = some ((∅ : Store).insert x (.bool b)) := by
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, List.length_drop, htlen]; omega
  have hw : ABI.bytesToWord (((cd.toList.drop 4).drop 0).take 32) = if b then ⟨1⟩ else ⟨0⟩ := by
    rw [List.drop_zero, decode_word_at_eq cd 4 (by omega) (by norm_num)]
    exact hword
  rw [decodeCalldataWithMode_vyperScalarWords_eq (by decide), if_neg (by rw [htlen]; omega)]
  cases b with
  | false =>
    simp only [decodeScalarWords?]
    rw [decodeScalarWord_bool_ok_zero htake hw]
    rfl
  | true =>
    simp only [decodeScalarWords?]
    rw [decodeScalarWord_bool_ok_one htake hw]
    rfl

-- LIBRARY CANDIDATE: Vyper Boolean calldata rejects noncanonical words.
theorem decodeCalldataWithMode_vyper_bool_none_noncanon {cd : ByteArray} {x : Solm.Ident}
    (hsz : 36 ≤ cd.size) (hz : calldataWord cd 4 ≠ ⟨0⟩) (ho : calldataWord cd 4 ≠ ⟨1⟩) :
    decodeCalldataWithMode .vyper [x] [.elem .bool] cd = none := by
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake : (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, List.length_drop, htlen]; omega
  have hw : ABI.bytesToWord (((cd.toList.drop 4).drop 0).take 32) = calldataWord cd 4 := by
    rw [List.drop_zero, decode_word_at_eq cd 4 (by omega) (by norm_num)]
  rw [decodeCalldataWithMode_vyperScalarWords_eq (by decide), if_neg (by rw [htlen]; omega)]
  simp only [decodeScalarWords?]
  rw [decodeScalarWord_bool_none_noncanon htake (by rw [hw]; exact hz) (by rw [hw]; exact ho)]
  rfl

-- LIBRARY CANDIDATE: a Vyper Boolean argument requires one complete word.
theorem decodeCalldataWithMode_vyper_bool_none_short {cd : ByteArray} {x : Solm.Ident}
    (hshort : cd.size < 36) : decodeCalldataWithMode .vyper [x] [.elem .bool] cd = none := by
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldataWithMode_vyperScalarWords_eq (by decide)]
  by_cases hsz : cd.size < 4
  · rw [if_pos (by rw [htlen]; omega)]
  · rw [if_neg (by rw [htlen]; omega)]
    simp only [decodeScalarWords?]
    rw [decodeScalarWord_bool_none_short (by rw [List.drop_zero, List.length_take, List.length_drop, htlen]; omega)]
    rfl
end Benchmarks.CurveVault
