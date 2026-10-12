import Benchmarks.EAS.EAS.DelegatedAttestationDecode
import Benchmarks.EAS.EAS.RequestArrayElements
import Benchmarks.EAS.EAS.SignatureCalldata
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem requestData_retained_decode (cd : ByteArray) (ptr : UInt256) (tailAccess : Bool) :
    decodeValue? requestDataABI cd.toList ptr.toNat delegatedAttestationMaterializedPlan tailAccess =
      if requestDataValid cd ptr then some (requestDataRecord cd ptr).tuple else none := by
  rw [← requestData_decode cd ptr tailAccess]
  rw [requestDataABI,decodeValue?,decodeValue?]
  simp only [show abiTupleHeadSize? requestDataFields=some 192 by native_decide,
    show isDynamicABIType (.tuple requestDataFields)=true by native_decide,
    show isMemory delegatedAttestationMaterializedPlan=true from rfl,
    show isMemory ({} : CalldataPlan)=true from rfl,
    show (List.range requestDataFields.length).map (fun i => child delegatedAttestationMaterializedPlan (.field i))=
      [{},{},{},{},{},{}] by native_decide,
    show (List.range requestDataFields.length).map (fun i => child ({} : CalldataPlan) (.field i))=
      [{},{},{},{},{},{}] by native_decide]

theorem signature_retained_decode (cd : ByteArray) (ptr : UInt256) (tailAccess : Bool) :
    decodeValue? signatureABI cd.toList ptr.toNat delegatedAttestationMaterializedPlan tailAccess =
      if signatureAtValid cd ptr then some (signatureAt cd ptr).tuple else none := by
  rw [← signatureAt_decode_cases cd ptr tailAccess]
  rw [signatureABI,decodeValue?,decodeValue?]
  simp only [show abiTupleHeadSize? [abiUInt8,abiBytes32,abiBytes32]=some 96 by native_decide,
    show isDynamicABIType (.tuple [abiUInt8,abiBytes32,abiBytes32])=false from rfl,
    show isMemory delegatedAttestationMaterializedPlan=true from rfl,
    show isMemory ({} : CalldataPlan)=true from rfl,Bool.not_false,Bool.true_eq,if_true]

def delegatedAttestationDataValid (cd : ByteArray) (offset : UInt256) (i : Nat) : Prop :=
  requestReferenceValid cd offset (UInt256.ofNat (offset.toNat+32*i)) ∧
    requestDataValid cd (requestArrayElement cd offset i)
instance (cd : ByteArray) (offset : UInt256) (i : Nat) : Decidable (delegatedAttestationDataValid cd offset i) :=
  inferInstanceAs (Decidable (_ ∧ _))
def delegatedAttestationDatum (cd : ByteArray) (offset : UInt256) (i : Nat) : Value :=
  if delegatedAttestationDataValid cd offset i then (requestDataRecord cd (requestArrayElement cd offset i)).tuple else decodeFailure

def delegatedAttestationSignature (cd : ByteArray) (offset : UInt256) (i : Nat) : Value :=
  if signatureAtValid cd (UInt256.ofNat (offset.toNat+96*i)) then
    (signatureAt cd (UInt256.ofNat (offset.toNat+96*i))).tuple else decodeFailure

theorem delegatedAttestationData_element (cd : ByteArray) (offset : UInt256) (i : Nat)
    (hb : offset.toNat+32*i < UInt256.size) :
    retainedArrayElement requestDataABI delegatedAttestationArrayPlan cd.toList offset.toNat 32 i =
      delegatedAttestationDatum cd offset i := by
  have hslot : solcAdd offset.toNat (32*i)=(UInt256.ofNat (offset.toNat+32*i)).toNat := rfl
  have href := requestReference_decode cd offset (UInt256.ofNat (offset.toNat+32*i))
  rw [ulit_toNat' _ hb] at href
  change solcTailTarget? true requestDataABI cd.toList offset.toNat (offset.toNat+32*i) =
    if requestReferenceValid cd offset (UInt256.ofNat (offset.toNat+32*i)) then
      some (requestArrayElement cd offset i).toNat else none at href
  simp only [retainedArrayElement,show isDynamicABIType requestDataABI=true by native_decide,
    show isMemory delegatedAttestationArrayPlan=false from rfl,
    show child delegatedAttestationArrayPlan .element=delegatedAttestationMaterializedPlan from rfl,
    Bool.not_false,Bool.true_and,if_true,hslot,ulit_toNat' _ hb,href,bind]
  by_cases hr : requestReferenceValid cd offset (UInt256.ofNat (offset.toNat+32*i))
  · rw [if_pos hr]
    simp only [Option.bind_some,requestData_retained_decode]
    by_cases hv : requestDataValid cd (requestArrayElement cd offset i) <;>
      simp only [hv,if_true,if_false,Option.getD_some,Option.getD_none,delegatedAttestationDatum,
        delegatedAttestationDataValid,hr,hv,and_self,and_false,if_true,if_false]
  · simp only [if_neg hr,Option.bind_none,Option.getD_none,delegatedAttestationDatum,
      delegatedAttestationDataValid,hr,false_and,if_false]

theorem delegatedAttestationSignature_element (cd : ByteArray) (offset : UInt256) (i : Nat) :
    retainedArrayElement signatureABI delegatedAttestationArrayPlan cd.toList offset.toNat 96 i =
      delegatedAttestationSignature cd offset i := by
  have hslot : solcAdd offset.toNat (96*i)=(UInt256.ofNat (offset.toNat+96*i)).toNat := rfl
  simp only [retainedArrayElement,show isDynamicABIType signatureABI=false from rfl,
    show child delegatedAttestationArrayPlan .element=delegatedAttestationMaterializedPlan from rfl,
    Bool.false_eq_true,if_false,Bool.false_and,bind,Option.bind_some,hslot,signature_retained_decode]
  by_cases hv : signatureAtValid cd (UInt256.ofNat (offset.toNat+96*i)) <;>
    simp only [hv,if_true,if_false,Option.getD_some,Option.getD_none,delegatedAttestationSignature]

theorem delegatedAttestationArrayValues_length (ty : ABIType) (cd : ByteArray) (header : UInt256) (stride : Nat) :
    (delegatedAttestationArrayValues ty cd header stride).length=(calldataWord cd header.toNat).toNat := by
  simp only [delegatedAttestationArrayValues,retainedArrayValues,List.length_map,List.length_range]

theorem delegatedAttestationData_get (cd : ByteArray) (header : UInt256) (i : Nat)
    (hi : i < (delegatedAttestationArrayValues requestDataABI cd header 32).length)
    (hb : (header+UInt256.ofNat 32).toNat+32*i < UInt256.size) :
    (delegatedAttestationArrayValues requestDataABI cd header 32)[i]=
      delegatedAttestationDatum cd (header+UInt256.ofNat 32) i := by
  simp only [delegatedAttestationArrayValues,retainedArrayValues,List.getElem_map,List.getElem_range]
  exact delegatedAttestationData_element cd _ i hb

theorem delegatedAttestationSignature_get (cd : ByteArray) (header : UInt256) (i : Nat)
    (hi : i < (delegatedAttestationArrayValues signatureABI cd header 96).length) :
    (delegatedAttestationArrayValues signatureABI cd header 96)[i]=
      delegatedAttestationSignature cd (header+UInt256.ofNat 32) i := by
  simp only [delegatedAttestationArrayValues,retainedArrayValues,List.getElem_map,List.getElem_range]
  exact delegatedAttestationSignature_element cd _ i

end Benchmarks.EAS.EAS
