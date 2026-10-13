import Benchmarks.EAS.EAS.AttestationValues
import Benchmarks.EAS.EAS.GetAttestationSource
import Reasoning.ABIViews
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem encodeABIValue_uint (width : ABI.BitWidth) (v : UInt256)
    (hlt : v.toNat < EVM.twoPow width.val) :
    encodeABIValue? (.elem (.int (.uint width))) (.int (Int.ofNat v.toNat)) =
      some (EVM.Word.toBytesBE v) := by
  have hword : EVM.word v.toNat = v := u256_ofNat_toNat v
  have hcond : 0 ≤ Int.ofNat v.toNat ∧ Int.ofNat v.toNat < Int.ofNat (EVM.twoPow width.val) :=
    ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr hlt⟩
  simp only [encodeABIValue?, encodeABIWord?, if_neg (Nat.ne_of_gt width.property.1), if_pos hcond,
    hword, bind, Option.bind, pure]
  change some (EVM.Word.toBytesBE (EVM.word v.toNat)) = _
  rw [hword]

theorem encodeABIValue_boolWord (word : UInt256) :
    encodeABIValue? (.elem .bool) (wordToElem .bool word) =
      some (EVM.Word.toBytesBE (UInt256.isZero (UInt256.isZero word))) := by
  rw [wordToElemBool, encodeABIValue_bool]
  by_cases hz : word = ⟨0⟩
  · simp only [hz, decide_true, Bool.not_true]; rfl
  · simp only [hz, decide_false, Bool.not_false, isZero_eq_zero_of_ne hz]; rfl

theorem wordShiftRight_zero (word : UInt256) : UInt256.shiftRight word (UInt256.ofNat 0) = word := by
  rw [wordShiftRight_div word 0 (by decide)]
  apply u256_inj
  change word.toNat / 1 = word.toNat
  omega

def attestationReturnBytes (evm : EVM.State) (word : UInt256) : ByteArray :=
  wordBytes (⟨32⟩ :: (storedAttestationWords evm.accountMap evm.executionEnv (dbSlot word) ++
    [⟨320⟩, UInt256.ofNat (attestationPayload evm word).size])) ++
  (attestationPayload evm word ++ ByteArray.zeroes (32*(((attestationPayload evm word).size+31)/32)-(attestationPayload evm word).size))

theorem attestationTupleEncoding (evm : EVM.State) (word : UInt256) :
    encodeABIValue? attestationABI (getAttestationTuple evm word) =
      some ((wordBytes (storedAttestationWords evm.accountMap evm.executionEnv (dbSlot word))).toList ++
        ABI.natBytes 320 ++ ABI.natBytes (attestationPayload evm word).size ++
          ABI.padRightToWord (attestationPayload evm word).toList) := by
  have hu (w : UInt256) : encodeABIValue? (.elem (.int (.uint ⟨64, by decide⟩)))
      (.int (Int.ofNat (UInt256.land w ⟨18446744073709551615⟩).toNat)) =
        some (EVM.Word.toBytesBE (UInt256.land w ⟨18446744073709551615⟩)) :=
    encodeABIValue_uint _ _ (u256LandMaskToNatLtOfToNat _ _ (by decide))
  have hb (w : UInt256) : encodeABIValue? (.elem (.bytes abiBytes32Width))
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE w)) = some (EVM.Word.toBytesBE w) := by
    simpa only [toByteArray_eq_toBytesBE, byteArray_toList_eq, List.toList_toArray] using encodeABIValue_bytes32_word w
  have hd (b : ByteArray) : encodeABIValue? .bytes (.bytes b) = some (ABI.natBytes b.size ++ ABI.padRightToWord b.toList) := by rw [encodeABIValue?]
  rw [attestationABI, getAttestationTuple, encodeABIValue?, encodeABIValues?]
  simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, Option.bind, bind,
    Option.pure_def, Option.map, pure]
  simp only [attestationStoredFields, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    storageLocLoad_bytes32, attestationU64_read, storageLocLoad_address_offset0, attestationBool_read]
  simp only [encodeABIValuesFrom?, hb, hd, hu, encodeABIValue_addr_masked,
    encodeABIValue_boolWord, isDynamicABIType, Option.bind, bind, Option.pure_def, pure,
    Bool.false_eq_true, if_false, if_true, List.nil_append, List.append_nil, List.length_nil, Nat.add_zero]
  simp only [storedAttestationWords, wordBytes, ByteArray.data_append, Array.toList_append, ByteArray.empty, Array.toList_empty,
    List.append_nil, List.append_assoc, toByteArray_eq_toBytesBE, byteArray_toList_eq, List.toList_toArray]
  rw [show (8 * (0 : Fin 32).val) = 0 from rfl, wordShiftRight_zero]
  rfl


theorem attestationReturnEncoding (evm : EVM.State) (word : UInt256) :
    encodeReturnValue? attestationABI (getAttestationTuple evm word) = some (attestationReturnBytes evm word) := by
  have hd : isDynamicABIType attestationABI = true := by decide
  have hh : abiTupleHeadSize? [attestationABI] = some 32 := by
    simp only [abiTupleHeadSize?, staticABIEncodedSize?, hd, Option.bind, bind]
    rfl
  change encodeReturnValues? [attestationABI] [getAttestationTuple evm word] = _
  simp only [encodeReturnValues?, encodeABIValues?, hh, encodeABIValuesFrom?, attestationTupleEncoding,
    hd, if_true, bind, Option.bind, List.length_nil, Nat.add_zero, List.nil_append, List.append_nil]
  simp only [attestationReturnBytes, wordBytes, wordBytes_append,
    ← bytearray_append_list_eq, natBytes_toByteArray, padRightToWord_toByteArray,
    ABI.paddedSize, ByteArray.append_empty, ByteArray.append_assoc]
  apply congrArg some
  apply byteArray_eq_of_toList_eq
  simp only [byteArray_toList_eq, List.toList_toArray, ByteArray.data_append, Array.toList_append,
    toByteArray_eq_toBytesBE, List.append_assoc, byteArray_zeroes_toList]
  simp only [ABI.natBytes, ABI.padRightToWord, ABI.zeroBytes, ABI.paddedSize, Array.length_toList, Nat.mul_comm]
  rfl

end Benchmarks.EAS.EAS
