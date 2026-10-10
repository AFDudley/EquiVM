import Benchmarks.EAS.EAS.ScalarDecode
import Reasoning.ABIComposite
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: bounded return lengths make the solc 0.8 scalar decoder agree with the modern decoder.
theorem decodeReturnSolc08Scalar_eq (table : List (Nat × List ABI.CalldataPlan))
    (ty : ABI.ElemType) (out : ByteArray) (hscalar : isABIScalarWordType (.elem ty) = true)
    (hb : out.size < 2^255) :
    ABI.decodeReturnValueWithMode? (.solc08Calldata table) (.elem ty) out =
      ABI.decodeReturnValue? (.elem ty) out := by
  have hlen : out.toList.length = out.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hword : (EVM.Word.ofNat out.size).toNat = out.size := ulit_toNat' _ (by change out.size < 2^256; omega)
  have hcheck : ABI.Solc08Calldata.solcSLT out.size 32 = decide (out.size < 32) := by
    change decide ((if (EVM.Word.ofNat out.size).toNat < 2^255 then Int.ofNat (EVM.Word.ofNat out.size).toNat else
      Int.ofNat (EVM.Word.ofNat out.size).toNat-Int.ofNat (2^256)) < (32 : Int)) = _
    rw [hword, if_pos hb]
    congr 1
    apply propext
    simp only [Int.ofNat_eq_natCast]
    omega
  unfold ABI.decodeReturnValueWithMode? ABI.decodeReturnValue?
  rw [decodeReturnValues_scalarWords_eq (by simpa only [List.all_cons, List.all_nil, hscalar, Bool.true_and])]
  simp only [List.isEmpty_cons, Bool.false_eq_true, hlen, show ¬ 2^255 ≤ out.size by omega, and_false, if_false]
  simp only [ABI.Solc08Calldata.decodeReturns?, abiTupleHeadSize?, staticABIEncodedSize?,
    isDynamicABIType, List.isEmpty_cons, Bool.not_false, Bool.true_and, Bool.false_eq_true, if_false, Nat.add_zero, bind, Option.bind, hcheck]
  by_cases hs : out.size < 32
  · have hn : ¬ ((out.toList.drop 0).take 32).length = 32 := by simp only [List.drop_zero, List.length_take, hlen]; omega
    have hd : decodeScalarWord? (.elem ty) out.toList 0 = none := by
      simp only [decodeScalarWord?, readWord?, readBytes?, if_neg hn, bind, Option.bind]
    simp only [hs, decide_true, if_true, decodeScalarWords?, hd, bind, Option.bind]
  · have ht : (out.toList.take 32).length = 32 := by rw [List.length_take, hlen, Nat.min_eq_left (by omega)]
    have hr : ABI.Solc08Calldata.solcReadBytes out.toList 0 32 = out.toList.take 32 := by
      simp only [ABI.Solc08Calldata.solcReadBytes, Nat.zero_mod, List.drop_zero, ht, Nat.sub_self, List.replicate_zero, List.append_nil]
    simp only [hs, decide_false, Bool.false_eq_true, if_false, ABI.Solc08Calldata.decodeFields?,
      ABI.Solc08Calldata.stride?, isDynamicABIType, staticABIEncodedSize?,
      ABI.Solc08Calldata.retainFailure, List.headD_nil, List.tail_nil,
      ABI.Solc08Calldata.decodeValue?, ABI.Solc08Calldata.solcAdd, Nat.zero_add, Nat.zero_mod,
      hr, bind, Option.bind]
    rw [decodeABIValue_scalarWord_eq hscalar]
    have hd : decodeScalarWord? (.elem ty) (out.toList.take 32) 0 = decodeScalarWord? (.elem ty) out.toList 0 := by
      simp only [decodeScalarWord?, readWord?, readBytes?, List.drop_zero, List.take_take, Nat.min_self]
    rw [hd]
    simp only [List.contains_nil, Bool.false_eq_true, if_false, decodeScalarWords?, bind, Option.bind]
    cases decodeScalarWord? (.elem ty) out.toList 0 <;> rfl

theorem easDecodeReturnBool_valid {out : ByteArray} (hv : BoolReturnValid out)
    (hb : out.size < 2^255) :
    ABI.decodeReturnValueWithMode? config.abiDecodeMode abiBool out =
      some (.bool (decide (calldataWord out 0 ≠ ⟨0⟩))) := by
  change ABI.decodeReturnValueWithMode? (.solc08Calldata easPlanTable) abiBool out = _
  rw [decodeReturnSolc08Scalar_eq easPlanTable .bool out (by decide) hb]
  exact decodeReturnBool_valid hv hb

theorem easDecodeReturnBool_invalid {out : ByteArray} (hv : ¬ BoolReturnValid out)
    (hb : out.size < 2^255) :
    ABI.decodeReturnValueWithMode? config.abiDecodeMode abiBool out = none := by
  change ABI.decodeReturnValueWithMode? (.solc08Calldata easPlanTable) abiBool out = _
  rw [decodeReturnSolc08Scalar_eq easPlanTable .bool out (by decide) hb]
  exact decodeReturnBool_invalid hv hb

end Benchmarks.EAS.EAS
