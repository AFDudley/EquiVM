import Benchmarks.EAS.EAS.RetainedArrayDecode
import Benchmarks.EAS.EAS.DelegatedRevocationDecode
import Benchmarks.EAS.EAS.MultiRequestControl
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def delegatedAttestationRowPlan : CalldataPlan := child DelegatedBatchSite.attest.plan .element
def delegatedAttestationArrayPlan : CalldataPlan := {materialize := [[.element]],deferErrors := [[],[.element]]}
def delegatedAttestationMaterializedPlan : CalldataPlan := {deferErrors := [[]]}

def delegatedAttestationArrayReferenceValid (cd : ByteArray) (root : UInt256) (field : Nat) : Prop :=
  UInt256.isZero (UInt256.slt (calldataWord cd (root+UInt256.ofNat field).toNat)
    ((UInt256.ofNat cd.size-root)-⟨31⟩)) = ⟨0⟩
instance (cd : ByteArray) (root : UInt256) (field : Nat) : Decidable (delegatedAttestationArrayReferenceValid cd root field) :=
  inferInstanceAs (Decidable (_ = _))

def delegatedAttestationArrayValues (ty : ABIType) (cd : ByteArray) (header : UInt256) (stride : Nat) : List Value :=
  retainedArrayValues ty delegatedAttestationArrayPlan cd.toList (header+UInt256.ofNat 32).toNat stride
    (calldataWord cd header.toNat).toNat
def delegatedAttestationArrayValue (ty : ABIType) (cd : ByteArray) (root : UInt256) (field stride : Nat) : Value :=
  if delegatedAttestationArrayReferenceValid cd root field ∧ referencedArrayHeadValid cd (delegatedBatchArray cd root field) stride then
    .array (delegatedAttestationArrayValues ty cd (delegatedBatchArray cd root field) stride) else decodeFailure
def delegatedAttestationAddressValue (cd : ByteArray) (root : UInt256) : Value :=
  if delegatedBatchAddressClean cd root then .address (AccountAddress.ofNat (calldataWord cd (root+UInt256.ofNat 96).toNat).toNat)
    else decodeFailure
def delegatedAttestationTuple (cd : ByteArray) (root : UInt256) : Value :=
  .tuple [wordBytes32Value (calldataWord cd root.toNat),
    delegatedAttestationArrayValue requestDataABI cd root 32 32,
    delegatedAttestationArrayValue signatureABI cd root 64 96,delegatedAttestationAddressValue cd root]

theorem delegatedAttestationArrayField_decode {ty : ABIType} {stride : Nat}
    (hs : stride? ty=some stride) (hn : (ty == .elem .bool)=false)
    (cd : ByteArray) (root : UInt256) (field : Nat) :
    retainFailure delegatedAttestationArrayPlan (do
      let target ← solcTailTarget? true (.dynamicArray ty) cd.toList root.toNat (root+UInt256.ofNat field).toNat
      decodeValue? (.dynamicArray ty) cd.toList target delegatedAttestationArrayPlan true) =
      some (delegatedAttestationArrayValue ty cd root field stride) := by
  have href := solcTailTarget_reference cd root (root+UInt256.ofNat field) ⟨32⟩ (.dynamicArray ty) rfl
  change solcTailTarget? true (.dynamicArray ty) cd.toList root.toNat (root+UInt256.ofNat field).toNat =
    if delegatedAttestationArrayReferenceValid cd root field then some (delegatedBatchArray cd root field).toNat else none at href
  simp only [href,retainFailure,show delegatedAttestationArrayPlan.deferErrors.contains []=true from rfl,if_true,bind]
  by_cases hr : delegatedAttestationArrayReferenceValid cd root field
  · rw [if_pos hr]
    simp only [Option.bind_some]
    rw [referencedRetainedArray_decode hs hn (by rfl) (by rfl)]
    by_cases hh : referencedArrayHeadValid cd (delegatedBatchArray cd root field) stride
    · simp only [if_pos hh,delegatedAttestationArrayValue,hr,hh,and_self,if_true,Option.getD_some,delegatedAttestationArrayValues]
    · simp only [if_neg hh,delegatedAttestationArrayValue,hr,hh,and_false,if_false,Option.getD_none]
  · simp only [if_neg hr,Option.bind_none,Option.getD_none,delegatedAttestationArrayValue,hr,false_and,if_false]

theorem delegatedAttestationRow_decode (cd : ByteArray) (root : UInt256) :
    decodeValue? DelegatedBatchSite.attest.abi cd.toList root.toNat delegatedAttestationRowPlan true =
      some (delegatedAttestationTuple cd root) := by
  have hp : (List.range 4).map (fun i => child delegatedAttestationRowPlan (.field i)) =
      [{materialize := []},delegatedAttestationArrayPlan,delegatedAttestationArrayPlan,{materialize := [],deferErrors := [[]]}] := by native_decide
  have h0 : solcAdd root.toNat 0=root.toNat := Nat.mod_eq_of_lt root.val.isLt
  have h32 : solcAdd root.toNat 32=(root+UInt256.ofNat 32).toNat := solcAdd_word root (UInt256.ofNat 32)
  have h64 : solcAdd root.toNat 64=(root+UInt256.ofNat 64).toNat := solcAdd_word root (UInt256.ofNat 64)
  have h96 : solcAdd root.toNat 96=(root+UInt256.ofNat 96).toNat := solcAdd_word root (UInt256.ofNat 96)
  rw [DelegatedBatchSite.abi,decodeValue?]
  simp only [show abiTupleHeadSize? [abiBytes32,.dynamicArray requestDataABI,.dynamicArray signatureABI,.elem .address]=some 128 by native_decide,
    show isMemory delegatedAttestationRowPlan=false from rfl,
    show isDynamicABIType (.tuple [abiBytes32,.dynamicArray requestDataABI,.dynamicArray signatureABI,.elem .address])=true from rfl,
    Bool.not_true,Bool.false_or,Bool.false_and,Bool.false_eq_true,if_false,bind,Option.bind_some,
    List.length_cons,List.length_nil,hp]
  simp only [decodeFields?,show stride? abiBytes32=some 32 from rfl,
    show stride? (.dynamicArray requestDataABI)=some 32 from rfl,
    show stride? (.dynamicArray signatureABI)=some 32 from rfl,
    show stride? (.elem .address)=some 32 from rfl,
    show isDynamicABIType abiBytes32=false from rfl,
    show isDynamicABIType (.dynamicArray requestDataABI)=true from rfl,
    show isDynamicABIType (.dynamicArray signatureABI)=true from rfl,
    show isDynamicABIType (.elem .address)=false from rfl,
    List.headD_cons,List.tail_cons,Bool.not_false,Bool.true_and,Bool.false_and,Bool.false_eq_true,
    if_true,if_false,bind,Option.bind_some,Nat.zero_add,Nat.reduceAdd,h0,h32,h64,h96]
  have hdata := delegatedAttestationArrayField_decode (ty := requestDataABI) (stride := 32) (by native_decide) rfl cd root 32
  have hsig := delegatedAttestationArrayField_decode (ty := signatureABI) (stride := 96) (by native_decide) rfl cd root 64
  simp only [bind] at hdata hsig
  rw [decodeSolcBytes32_total cd root {materialize := []} false,hdata,hsig,
    decodeSolcScalar_total cd (root+UInt256.ofNat 96) .address {materialize := [],deferErrors := [[]]} false rfl]
  simp only [retainFailure,show ({materialize := []} : CalldataPlan).deferErrors.contains []=false from rfl,
    show ({materialize := [],deferErrors := [[]]} : CalldataPlan).deferErrors.contains []=true from rfl,
    if_false,if_true,Option.bind_some,pure,delegatedAttestationTuple]
  change some (Value.tuple [_,_,_,(if delegatedBatchAddressClean cd root then
    some (.address (AccountAddress.ofNat (calldataWord cd (root+UInt256.ofNat 96).toNat).toNat)) else none).getD decodeFailure]) = _
  by_cases ha : delegatedBatchAddressClean cd root <;> simp only [ha,if_true,if_false,Option.getD_some,Option.getD_none,delegatedAttestationAddressValue]

theorem delegatedAttestationElement_decode (cd : ByteArray) (base : UInt256) (i : Nat)
    (hb : base.toNat+32*i < UInt256.size) :
    delegatedBatchElementDecode .attest cd base i =
      if delegatedBatchReferenceValid cd base i then some (delegatedAttestationTuple cd (multiRequestRoot cd base i)) else none := by
  have hslot : solcAdd base.toNat (32*i)=(UInt256.ofNat (base.toNat+32*i)).toNat := rfl
  have href := solcTailTarget_reference cd base (UInt256.ofNat (base.toNat+32*i)) ⟨128⟩ DelegatedBatchSite.attest.abi (by native_decide)
  rw [ulit_toNat' _ hb] at href
  change solcTailTarget? true DelegatedBatchSite.attest.abi cd.toList base.toNat (base.toNat+32*i) =
    if delegatedBatchReferenceValid cd base i then some (multiRequestRoot cd base i).toNat else none at href
  simp only [delegatedBatchElementDecode,hslot,ulit_toNat' _ hb,href,bind]
  by_cases hr : delegatedBatchReferenceValid cd base i
  · simp only [if_pos hr,Option.bind_some]; exact delegatedAttestationRow_decode cd _
  · simp only [if_neg hr,Option.bind_none]

end Benchmarks.EAS.EAS
