import Benchmarks.CurveVault.Calls

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

theorem decodeReturn_vyper_bool_ok (out : ByteArray) (h32 : 32 ≤ out.size) (value : Bool)
    (hword : retWord out = value.toUInt256) :
    ABI.decodeReturnValueWithMode? .vyper (.elem .bool) out = some (.bool value) := by
  have hlen : ((out.toList.drop 0).take 32).length = 32 := by
    simp only [List.drop_zero, List.length_take, byteArray_toList_eq, Array.length_toList]
    exact Nat.min_eq_left h32
  rw [decodeReturn_vyper_scalar _ _ rfl]
  cases value with
  | false =>
      rw [decodeScalarWord_bool_ok_zero hlen (by rw [bytesToWord_take32_retWord]; exact hword)]
      rfl
  | true =>
      rw [decodeScalarWord_bool_ok_one hlen (by rw [bytesToWord_take32_retWord]; exact hword)]
      rfl

theorem decodeReturn_vyper_bool_noncanon (out : ByteArray) (h32 : 32 ≤ out.size)
    (hzero : retWord out ≠ ⟨0⟩) (hone : retWord out ≠ ⟨1⟩) :
    ABI.decodeReturnValueWithMode? .vyper (.elem .bool) out = none := by
  have hlen : ((out.toList.drop 0).take 32).length = 32 := by
    simp only [List.drop_zero, List.length_take, byteArray_toList_eq, Array.length_toList]
    exact Nat.min_eq_left h32
  rw [decodeReturn_vyper_scalar _ _ rfl,
    decodeScalarWord_bool_none_noncanon hlen
      (by rw [bytesToWord_take32_retWord]; exact hzero)
      (by rw [bytesToWord_take32_retWord]; exact hone)]
  rfl

theorem decodeReturn_vyper_bool_short (out : ByteArray) (h32 : out.size < 32) :
    ABI.decodeReturnValueWithMode? .vyper (.elem .bool) out = none := by
  have hlen : ¬ ((out.toList.drop 0).take 32).length = 32 := by
    simp only [List.drop_zero, List.length_take, byteArray_toList_eq, Array.length_toList]
    change ¬ min 32 out.size = 32
    omega
  rw [decodeReturn_vyper_scalar _ _ rfl, decodeScalarWord_bool_none_short hlen]
  rfl

end Benchmarks.CurveVault
