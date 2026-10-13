import Benchmarks.EAS.EAS.CalldataScalar
import Benchmarks.EAS.EAS.CalldataGuards
import Benchmarks.EAS.EAS.CopyRequestFields
import Benchmarks.EAS.EAS.AttestationRequest
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def requestDataFields : List ABIType :=
  [.elem .address,.elem (.int (.uint ⟨64,by decide⟩)),.elem .bool,abiBytes32,.bytes,abiUInt256]
def requestDataABI : ABIType := .tuple requestDataFields
def requestDataTail (cd : ByteArray) (src : UInt256) : UInt256 := src+requestCopyWord cd src 128
def requestDataLength (cd : ByteArray) (src : UInt256) : UInt256 := calldataWord cd (requestDataTail cd src).toNat
def requestDataRecord (cd : ByteArray) (src : UInt256) : AttestationRequestRecord :=
  { recipient := AccountAddress.ofNat (calldataWord cd src.toNat).toNat
    expirationTime := requestCopyWord cd src 32
    revocable := decide ((requestCopyWord cd src 64).toNat ≠ 0)
    refUID := requestCopyWord cd src 96
    data := cd.readBytes ((requestDataTail cd src).toNat+32) (requestDataLength cd src).toNat
    value := requestCopyWord cd src 160 }
def requestDataPayloadValid (cd : ByteArray) (src : UInt256) : Prop :=
  UInt256.isZero (UInt256.slt (requestDataTail cd src+⟨31⟩) (UInt256.ofNat cd.size)) = ⟨0⟩ ∧
  (requestDataLength cd src).toNat ≤ solcMaxU64 ∧
  UInt256.gt ((requestDataTail cd src+requestDataLength cd src)+⟨32⟩) (UInt256.ofNat cd.size) = ⟨0⟩
instance (cd : ByteArray) (src : UInt256) : Decidable (requestDataPayloadValid cd src) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def requestDataValid (cd : ByteArray) (src : UInt256) : Prop :=
  UInt256.slt (UInt256.sub (UInt256.ofNat cd.size) src) ⟨192⟩ = ⟨0⟩ ∧
  requestCopyFieldsValid cd src ∧ requestDataPayloadValid cd src
instance (cd : ByteArray) (src : UInt256) : Decidable (requestDataValid cd src) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem requestDataFields_decode (cd : ByteArray) (src : UInt256) :
    decodeFields? requestDataFields cd.toList src.toNat 0 [{},{},{},{},{},{}] true = (do
      let recipient ← decodeABIWord? (.elem .address) (calldataWord cd src.toNat)
      let expiration ← decodeABIWord? (.elem (.int (.uint ⟨64,by decide⟩))) (requestCopyWord cd src 32)
      let revocable ← decodeABIWord? (.elem .bool) (requestCopyWord cd src 64)
      if solcMaxU64 < (requestCopyWord cd src 128).toNat then none else do
      let payload ← decodeValue? .bytes cd.toList (requestDataTail cd src).toNat {}
      some [recipient,expiration,revocable,wordBytes32Value (requestCopyWord cd src 96),payload,
        .int (Int.ofNat (requestCopyWord cd src 160).toNat)]) := by
  have h0 : solcAdd src.toNat 0 = src.toNat := Nat.mod_eq_of_lt src.val.isLt
  have hn (n : Nat) (h : n ≤ 160) : solcAdd src.toNat n = (src+UInt256.ofNat n).toNat := by
    have hb : (UInt256.ofNat n).toNat = n := ulit_toNat' n (by change n < 2^256; omega)
    simpa only [hb] using solcAdd_word src (UInt256.ofNat n)
  simp only [requestDataFields,decodeFields?,stride?,
    show isDynamicABIType abiBytes32 = false from rfl,
    show staticABIEncodedSize? abiBytes32 = some 32 from rfl,
    show isDynamicABIType abiUInt256 = false from rfl,
    show staticABIEncodedSize? abiUInt256 = some 32 from rfl,
    isDynamicABIType,staticABIEncodedSize?,bind,Option.bind,
    Bool.false_eq_true,if_false,if_true,List.headD_cons,List.tail_cons,retainFailure,
    List.contains_nil,Bool.not_true,Bool.false_and,Bool.true_and,solcTailTarget?,
    Nat.zero_add,Nat.reduceAdd,h0,hn 32 (by decide),hn 64 (by decide),hn 96 (by decide),
    hn 128 (by decide),hn 160 (by decide)]
  rw [decodeSolcScalar_total cd src .address {} false rfl,
    decodeSolcScalar_total cd (src+UInt256.ofNat 32) (.int (.uint ⟨64,by decide⟩)) {} false rfl,
    decodeSolcScalar_total cd (src+UInt256.ofNat 64) .bool {} false rfl,
    decodeSolcBytes32_total cd (src+UInt256.ofNat 96) {} false,
    solcReadNat_word_total cd (src+UInt256.ofNat 128),
    decodeSolcScalar_total cd (src+UInt256.ofNat 160) (.int (.uint ⟨256,by decide⟩)) {} false rfl]
  have hv : decodeABIWord? abiUInt256 (requestCopyWord cd src 160) =
      some (.int (Int.ofNat (requestCopyWord cd src 160).toNat)) := by
    change (if (requestCopyWord cd src 160).toNat < 2^256 then _ else _) = _
    rw [if_pos (show (requestCopyWord cd src 160).toNat < 2^256 from (requestCopyWord cd src 160).val.isLt)]
    rfl
  change decodeABIWord? abiUInt256 (calldataWord cd (src+UInt256.ofNat 160).toNat) = _ at hv
  rw [hv,solcAdd_word]
  simp only [requestCopyWord] at ⊢
  cases ha : decodeABIWord? (.elem .address) (calldataWord cd src.toNat) <;>
    cases he : decodeABIWord? (.elem (.int (.uint ⟨64,by decide⟩))) (calldataWord cd (src+UInt256.ofNat 32).toNat) <;>
    cases hb : decodeABIWord? (.elem .bool) (calldataWord cd (src+UInt256.ofNat 64).toNat) <;>
    simp only [Option.bind_some,Option.bind_none,ha,he,hb]
  by_cases ho : solcMaxU64 < (calldataWord cd (src+UInt256.ofNat 128).toNat).toNat
  · simp only [ho,if_true,Option.bind_none]
  · simp only [ho,if_false,Option.bind_some]
    simp only [requestDataTail,requestCopyWord]
    cases decodeValue? .bytes cd.toList (src+calldataWord cd (src+UInt256.ofNat 128).toNat).toNat {} <;> rfl

theorem requestDataFieldsValue_decode (cd : ByteArray) (src : UInt256) :
    (decodeFields? requestDataFields cd.toList src.toNat 0 [{},{},{},{},{},{}] true).map Value.tuple =
      if requestCopyFieldsValid cd src ∧ requestDataPayloadValid cd src then
        some (requestDataRecord cd src).tuple else none := by
  have hp : decodeValue? .bytes cd.toList (requestDataTail cd src).toNat {} =
      if requestDataPayloadValid cd src then
        some (.bytes (cd.readBytes ((requestDataTail cd src).toNat+32) (requestDataLength cd src).toNat)) else none := by
    simpa only [requestDataPayloadValid,requestDataLength] using decodeSolcBytes_total cd (requestDataTail cd src) {}
  have ha : decodeABIWord? (.elem .address) (calldataWord cd src.toNat) =
      if (calldataWord cd src.toNat).toNat < EVM.addressModulus then
        some (.address (AccountAddress.ofNat (calldataWord cd src.toNat).toNat)) else none := rfl
  rw [requestDataFields_decode,ha,decodeUIntWord_mask ⟨64,by decide⟩ _ easUint64Mask (by decide) (by decide),
    decodeBoolWord_clean,hp]
  by_cases ha : (calldataWord cd src.toNat).toNat < EVM.addressModulus
  · rw [if_pos ha]
    by_cases he : requestCopyWord cd src 32 = UInt256.land (requestCopyWord cd src 32) easUint64Mask
    · rw [if_pos he]
      by_cases hb : requestCopyWord cd src 64 = UInt256.isZero (UInt256.isZero (requestCopyWord cd src 64))
      · rw [if_pos hb]
        by_cases ho : (requestCopyWord cd src 128).toNat ≤ 2^64-1
        · have hn : ¬ solcMaxU64 < (requestCopyWord cd src 128).toNat := by change ¬ 18446744073709551615 < _; omega
          by_cases hd : requestDataPayloadValid cd src
          · rw [if_pos hd,if_pos ⟨⟨ha,he,hb,ho⟩,hd⟩]
            simp only [hn,if_false,dif_neg,bind,Option.bind_some,Option.bind_none,Option.map_some]
            rfl
          · rw [if_neg hd,if_neg (fun (h : requestCopyFieldsValid cd src ∧ requestDataPayloadValid cd src) => hd h.2)]
            simp only [hn,if_false,dif_neg,bind,Option.bind_some,Option.bind_none,Option.map_none]
        · have hn : solcMaxU64 < (requestCopyWord cd src 128).toNat := by change 18446744073709551615 < _; omega
          rw [if_neg (fun (h : requestCopyFieldsValid cd src ∧ requestDataPayloadValid cd src) => ho h.1.2.2.2)]
          simp only [hn,if_true,dif_pos,bind,Option.bind_some,Option.bind_none,Option.map_none]
      · rw [if_neg hb,if_neg (fun (h : requestCopyFieldsValid cd src ∧ requestDataPayloadValid cd src) => hb h.1.2.2.1)]
        rfl
    · rw [if_neg he,if_neg (fun (h : requestCopyFieldsValid cd src ∧ requestDataPayloadValid cd src) => he h.1.2.1)]
      rfl
  · rw [if_neg ha,if_neg (fun (h : requestCopyFieldsValid cd src ∧ requestDataPayloadValid cd src) => ha h.1.1)]
    rfl

theorem requestData_decode (cd : ByteArray) (src : UInt256) (tailAccess : Bool) :
    decodeValue? requestDataABI cd.toList src.toNat {} tailAccess =
      if requestDataValid cd src then some (requestDataRecord cd src).tuple else none := by
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq,Array.length_toList]; rfl
  have hs : solcSub cd.size src.toNat = (UInt256.sub (UInt256.ofNat cd.size) src).toNat := by
    unfold solcSub EVM.Word.ofNat
    rw [u256_ofNat_toNat]
    rfl
  rw [requestDataABI,decodeValue?]
  simp only [show abiTupleHeadSize? requestDataFields = some 192 by native_decide,
    show isDynamicABIType (.tuple requestDataFields) = true by native_decide,
    show isMemory ({} : CalldataPlan) = true from rfl,
    show (List.range requestDataFields.length).map (fun i => child ({} : CalldataPlan) (.field i)) =
      [{},{},{},{},{},{}] by native_decide,
    Bool.or_true,Bool.true_and,Bool.not_true,Bool.false_eq_true,if_false,bind,Option.bind,pure,
    hlen,hs]
  by_cases hh : UInt256.slt (UInt256.sub (UInt256.ofNat cd.size) src) ⟨192⟩ = ⟨0⟩
  · have hc : solcSLT (UInt256.sub (UInt256.ofNat cd.size) src).toNat 192 = false :=
      (solcSLT_word_false _ (⟨192⟩ : UInt256)).mpr hh
    rw [hc]
    simp only [Bool.false_eq_true,if_false]
    have he := requestDataFieldsValue_decode cd src
    simp only [requestDataValid,hh,true_and]
    cases hd : decodeFields? requestDataFields cd.toList src.toNat 0 [{},{},{},{},{},{}] true <;>
      rw [hd] at he <;> exact he
  · have hc : solcSLT (UInt256.sub (UInt256.ofNat cd.size) src).toNat 192 = true := by
      cases hb : solcSLT (UInt256.sub (UInt256.ofNat cd.size) src).toNat 192
      · exact False.elim (hh ((solcSLT_word_false _ (⟨192⟩ : UInt256)).mp hb))
      · rfl
    rw [hc]
    simp only [if_true]
    rw [if_neg (fun h => hh h.1)]

end Benchmarks.EAS.EAS
