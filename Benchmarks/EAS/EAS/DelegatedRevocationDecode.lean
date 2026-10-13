import Benchmarks.EAS.EAS.DelegatedBatchDecode
import Benchmarks.EAS.EAS.MemoryArrayTail
import Benchmarks.EAS.EAS.SchemaArrayDecode
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

structure DelegatedRevocationBatch where
  schema : UInt256
  data : List RevocationRequestRecord
  signatures : List SignatureRecord
  revoker : AccountAddress

def DelegatedRevocationBatch.tuple (r : DelegatedRevocationBatch) : Value :=
  .tuple [wordBytes32Value r.schema,.array (r.data.map RevocationRequestRecord.tuple),
    .array (r.signatures.map SignatureRecord.tuple),.address r.revoker]

def delegatedBatchArray (cd : ByteArray) (root : UInt256) (field : Nat) : UInt256 :=
  root+calldataWord cd (root+UInt256.ofNat field).toNat
def delegatedBatchArrayAccess (cd : ByteArray) (root : UInt256) (field : Nat) : Prop :=
  (calldataWord cd (root+UInt256.ofNat field).toNat).toNat ≤ solcMaxU64 ∧
    arrayHeaderReadable cd (delegatedBatchArray cd root field)
instance (cd : ByteArray) (root : UInt256) (field : Nat) : Decidable (delegatedBatchArrayAccess cd root field) :=
  inferInstanceAs (Decidable (_ ∧ _))
def delegatedBatchAddressClean (cd : ByteArray) (root : UInt256) : Prop :=
  (calldataWord cd (root+UInt256.ofNat 96).toNat).toNat < EVM.addressModulus
instance (cd : ByteArray) (root : UInt256) : Decidable (delegatedBatchAddressClean cd root) :=
  inferInstanceAs (Decidable (_ < _))

def decodeDelegatedRevocationFields (cd : ByteArray) (root : UInt256) : Option DelegatedRevocationBatch := do
  if ¬ delegatedBatchArrayAccess cd root 32 then none else do
  let rs ← decodeRevocationArray cd (delegatedBatchArray cd root 32)
  if ¬ delegatedBatchArrayAccess cd root 64 then none else do
  let ss ← decodeSignatureArray cd (delegatedBatchArray cd root 64)
  if ¬ delegatedBatchAddressClean cd root then none else
  some ⟨calldataWord cd root.toNat,rs,ss,AccountAddress.ofNat (calldataWord cd (root+UInt256.ofNat 96).toNat).toNat⟩

theorem delegatedRevocationFields_decode (cd : ByteArray) (root : UInt256) (hsize : cd.size < 2^255+4) :
    (decodeFields? [abiBytes32,.dynamicArray revocationDataABI,.dynamicArray signatureABI,.elem .address]
      cd.toList root.toNat 0 [{},{},{},{}] true).map Value.tuple =
      (decodeDelegatedRevocationFields cd root).map DelegatedRevocationBatch.tuple := by
  have h0 : solcAdd root.toNat 0 = root.toNat := Nat.mod_eq_of_lt root.val.isLt
  have hn (n : Nat) (h : n≤96) : solcAdd root.toNat n = (root+UInt256.ofNat n).toNat := by
    have hb : (UInt256.ofNat n).toNat = n := ulit_toNat' n (by change n<2^256; omega)
    simpa only [hb] using solcAdd_word root (UInt256.ofNat n)
  simp only [decodeFields?,show stride? abiBytes32 = some 32 from rfl,
    show stride? (.dynamicArray revocationDataABI) = some 32 from rfl,
    show stride? (.dynamicArray signatureABI) = some 32 from rfl,
    show stride? (.elem .address) = some 32 from rfl,
    show isDynamicABIType abiBytes32 = false from rfl,
    show isDynamicABIType (.dynamicArray revocationDataABI) = true from rfl,
    show isDynamicABIType (.dynamicArray signatureABI) = true from rfl,
    show isDynamicABIType (.elem .address) = false from rfl,
    bind,Option.bind,Bool.false_eq_true,if_false,if_true,List.headD_cons,List.tail_cons,retainFailure,
    List.contains_nil,Bool.not_true,Bool.false_and,Bool.true_and,solcTailTarget?,
    Nat.zero_add,Nat.reduceAdd,h0,hn 32 (by decide),hn 64 (by decide),hn 96 (by decide)]
  rw [decodeSolcBytes32_total cd root {} false,
    solcReadNat_word_total cd (root+UInt256.ofNat 32),solcReadNat_word_total cd (root+UInt256.ofNat 64)]
  rw [solcAdd_word,solcAdd_word]
  rw [decodeSolcScalar_total cd (root+UInt256.ofNat 96) .address {} false rfl]
  have ha : decodeABIWord? (.elem .address) (calldataWord cd (root+UInt256.ofNat 96).toNat) =
      if delegatedBatchAddressClean cd root then
        some (.address (AccountAddress.ofNat (calldataWord cd (root+UInt256.ofNat 96).toNat).toNat)) else none := rfl
  rw [ha]
  rw [decodeDelegatedRevocationFields]
  simp only [delegatedBatchArray]
  by_cases ho : (calldataWord cd (root+UInt256.ofNat 32).toNat).toNat ≤ solcMaxU64
  · rw [if_neg (by omega : ¬ solcMaxU64 < (calldataWord cd (root+UInt256.ofNat 32).toNat).toNat)]
    simp only [Option.bind_some]
    rw [memoryArray_tail,revocationArray_decode _ _ hsize]
    by_cases hr : arrayHeaderReadable cd (root+calldataWord cd (root+UInt256.ofNat 32).toNat)
    · rw [if_pos hr]
      rw [if_neg (not_not.mpr (show delegatedBatchArrayAccess cd root 32 from ⟨ho,hr⟩))]
      cases hd : decodeRevocationArray cd (root+calldataWord cd (root+UInt256.ofNat 32).toNat) with
      | none => rfl
      | some rs =>
        simp only [Option.map_some,bind,Option.bind_some]
        by_cases hs : (calldataWord cd (root+UInt256.ofNat 64).toNat).toNat ≤ solcMaxU64
        · rw [if_neg (by omega : ¬ solcMaxU64 < (calldataWord cd (root+UInt256.ofNat 64).toNat).toNat)]
          simp only [Option.bind_some]
          rw [memoryArray_tail,signatureArray_decode _ _ hsize]
          by_cases ht : arrayHeaderReadable cd (root+calldataWord cd (root+UInt256.ofNat 64).toNat)
          · rw [if_pos ht,if_neg (not_not.mpr (show delegatedBatchArrayAccess cd root 64 from ⟨hs,ht⟩))]
            cases hd : decodeSignatureArray cd (root+calldataWord cd (root+UInt256.ofNat 64).toNat) with
            | none => rfl
            | some ss =>
              by_cases hac : delegatedBatchAddressClean cd root
              · simp only [hac,not_true_eq_false,if_false,if_true]; rfl
              · simp only [hac,not_false_eq_true,if_false,if_true]; rfl
          · rw [if_neg ht,if_pos (fun h => ht h.2)]
            rfl
        · rw [if_pos (by omega : solcMaxU64 < (calldataWord cd (root+UInt256.ofNat 64).toNat).toNat),
            if_pos (show ¬ delegatedBatchArrayAccess cd root 64 from fun h => hs h.1)]
          rfl
    · rw [if_neg hr,if_pos (show ¬ delegatedBatchArrayAccess cd root 32 from fun h => hr h.2)]
      rfl
  · rw [if_pos (by omega : solcMaxU64 < (calldataWord cd (root+UInt256.ofNat 32).toNat).toNat),
      if_pos (show ¬ delegatedBatchArrayAccess cd root 32 from fun h => ho h.1)]
    rfl

def delegatedBatchHeadValid (cd : ByteArray) (root : UInt256) : Prop :=
  UInt256.slt (UInt256.sub (UInt256.ofNat cd.size) root) ⟨128⟩ = ⟨0⟩
instance (cd : ByteArray) (root : UInt256) : Decidable (delegatedBatchHeadValid cd root) :=
  inferInstanceAs (Decidable (_ = _))
def delegatedBatchReferenceValid (cd : ByteArray) (base : UInt256) (i : Nat) : Prop :=
  UInt256.isZero (UInt256.slt (calldataWord cd (base.toNat+32*i))
    ((UInt256.ofNat cd.size-base)-⟨127⟩)) = ⟨0⟩
instance (cd : ByteArray) (base : UInt256) (i : Nat) : Decidable (delegatedBatchReferenceValid cd base i) :=
  inferInstanceAs (Decidable (_ = _))
def decodeDelegatedRevocationAt (cd : ByteArray) (root : UInt256) : Option DelegatedRevocationBatch :=
  if delegatedBatchHeadValid cd root then decodeDelegatedRevocationFields cd root else none
def decodeDelegatedRevocation (cd : ByteArray) (base : UInt256) (i : Nat) : Option DelegatedRevocationBatch :=
  if delegatedBatchReferenceValid cd base i then decodeDelegatedRevocationAt cd (multiRequestRoot cd base i) else none

theorem delegatedRevocationRow_decode (cd : ByteArray) (root : UInt256) (hsize : cd.size < 2^255+4) :
    decodeValue? DelegatedBatchSite.revoke.abi cd.toList root.toNat (child DelegatedBatchSite.revoke.plan .element) true =
      (decodeDelegatedRevocationAt cd root).map DelegatedRevocationBatch.tuple := by
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq,Array.length_toList]; rfl
  have hs : solcSub cd.size root.toNat = (UInt256.sub (UInt256.ofNat cd.size) root).toNat := by
    unfold solcSub EVM.Word.ofNat
    rw [u256_ofNat_toNat]
    rfl
  rw [DelegatedBatchSite.abi,decodeValue?]
  simp only [show abiTupleHeadSize? [abiBytes32,.dynamicArray revocationDataABI,.dynamicArray signatureABI,.elem .address] = some 128 by native_decide,
    show isDynamicABIType (.tuple [abiBytes32,.dynamicArray revocationDataABI,.dynamicArray signatureABI,.elem .address]) = true by native_decide,
    show isMemory (child DelegatedBatchSite.revoke.plan .element) = true from rfl,
    show (List.range [abiBytes32,.dynamicArray revocationDataABI,.dynamicArray signatureABI,.elem .address].length).map
      (fun i => child (child DelegatedBatchSite.revoke.plan .element) (.field i)) = [{},{},{},{}] by native_decide,
    Bool.not_true,Bool.false_or,Bool.true_and,Bool.false_eq_true,if_false,
    bind,Option.bind_some,pure,hlen,hs]
  by_cases hh : delegatedBatchHeadValid cd root
  · have hc : solcSLT (UInt256.sub (UInt256.ofNat cd.size) root).toNat 128 = false :=
      (solcSLT_word_false _ (⟨128⟩ : UInt256)).mpr hh
    rw [hc]
    simp only [Bool.false_eq_true,if_false,decodeDelegatedRevocationAt,if_pos hh]
    have hf := delegatedRevocationFields_decode cd root hsize
    cases hd : decodeFields? [abiBytes32,.dynamicArray revocationDataABI,.dynamicArray signatureABI,.elem .address]
      cd.toList root.toNat 0 [{},{},{},{}] true <;> rw [hd] at hf <;> exact hf
  · have hc : solcSLT (UInt256.sub (UInt256.ofNat cd.size) root).toNat 128 = true := by
      cases hb : solcSLT (UInt256.sub (UInt256.ofNat cd.size) root).toNat 128
      · exact False.elim (hh ((solcSLT_word_false _ (⟨128⟩ : UInt256)).mp hb))
      · rfl
    rw [hc]
    simp only [if_true,decodeDelegatedRevocationAt,if_neg hh,Option.map_none]

theorem delegatedRevocationElement_decode (cd : ByteArray) (base : UInt256) (i : Nat)
    (hb : base.toNat+32*i < UInt256.size) (hsize : cd.size < 2^255+4) :
    delegatedBatchElementDecode .revoke cd base i =
      (decodeDelegatedRevocation cd base i).map DelegatedRevocationBatch.tuple := by
  have hslot : solcAdd base.toNat (32*i) = (UInt256.ofNat (base.toNat+32*i)).toNat := rfl
  have href := solcTailTarget_reference cd base (UInt256.ofNat (base.toNat+32*i)) ⟨128⟩
    DelegatedBatchSite.revoke.abi (by native_decide)
  rw [ulit_toNat' _ hb] at href
  change solcTailTarget? true DelegatedBatchSite.revoke.abi cd.toList base.toNat (base.toNat+32*i) =
    if delegatedBatchReferenceValid cd base i then some (multiRequestRoot cd base i).toNat else none at href
  simp only [delegatedBatchElementDecode,hslot,ulit_toNat' _ hb,href,bind]
  by_cases hr : delegatedBatchReferenceValid cd base i
  · simp only [if_pos hr,Option.bind_some,decodeDelegatedRevocation]
    exact delegatedRevocationRow_decode cd _ hsize
  · simp only [if_neg hr,decodeDelegatedRevocation,Option.map_none]
    rfl

end Benchmarks.EAS.EAS
