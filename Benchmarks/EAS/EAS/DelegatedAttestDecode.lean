import Benchmarks.EAS.EAS.SignatureCalldata
import Benchmarks.EAS.EAS.AttestDecode
import Benchmarks.EAS.EAS.VerifyAttestSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def delegatedAttestABI : ABIType := .tuple [abiBytes32,requestDataABI,signatureABI,.elem .address]
def delegatedAttestData (cd : ByteArray) (root : UInt256) : UInt256 := root+calldataWord cd (root+UInt256.ofNat 32).toNat
def delegatedAttestRecord (cd : ByteArray) (root : UInt256) : DelegatedAttestationRecord :=
  ⟨calldataWord cd root.toNat,requestDataRecord cd (delegatedAttestData cd root),
    signatureAt cd (root+UInt256.ofNat 64),AccountAddress.ofNat (calldataWord cd (root+UInt256.ofNat 160).toNat).toNat⟩
def delegatedAttestFieldsValid (cd : ByteArray) (root : UInt256) : Prop :=
  (calldataWord cd (root+UInt256.ofNat 32).toNat).toNat ≤ solcMaxU64 ∧
  requestDataValid cd (delegatedAttestData cd root) ∧ signatureAtValid cd (root+UInt256.ofNat 64) ∧
  (calldataWord cd (root+UInt256.ofNat 160).toNat).toNat < EVM.addressModulus
instance (cd : ByteArray) (root : UInt256) : Decidable (delegatedAttestFieldsValid cd root) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
def delegatedAttestRequestValid (cd : ByteArray) (root : UInt256) : Prop :=
  UInt256.slt (UInt256.sub (UInt256.ofNat cd.size) root) ⟨192⟩ = ⟨0⟩ ∧ delegatedAttestFieldsValid cd root
instance (cd : ByteArray) (root : UInt256) : Decidable (delegatedAttestRequestValid cd root) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem delegatedAttestFields_decode (cd : ByteArray) (root : UInt256) :
    (decodeFields? [abiBytes32,requestDataABI,signatureABI,.elem .address] cd.toList root.toNat 0 [{},{},{},{}] true).map Value.tuple =
      if delegatedAttestFieldsValid cd root then some (delegatedAttestRecord cd root).tuple else none := by
  have h0 : solcAdd root.toNat 0 = root.toNat := Nat.mod_eq_of_lt root.val.isLt
  have hn (n : Nat) (h : n ≤ 160) : solcAdd root.toNat n = (root+UInt256.ofNat n).toNat := by
    have hb : (UInt256.ofNat n).toNat = n := ulit_toNat' n (by change n < 2^256; omega)
    simpa only [hb] using solcAdd_word root (UInt256.ofNat n)
  simp only [decodeFields?,
    show stride? abiBytes32 = some 32 from rfl,show stride? requestDataABI = some 32 by native_decide,
    show stride? signatureABI = some 96 from rfl,show stride? (.elem .address) = some 32 from rfl,
    show isDynamicABIType abiBytes32 = false from rfl,show isDynamicABIType requestDataABI = true by native_decide,
    show isDynamicABIType signatureABI = false from rfl,show isDynamicABIType (.elem .address) = false from rfl,
    bind,Option.bind,Bool.false_eq_true,if_false,if_true,List.headD_cons,List.tail_cons,retainFailure,
    List.contains_nil,Bool.not_true,Bool.false_and,Bool.true_and,solcTailTarget?,
    Nat.zero_add,Nat.reduceAdd,h0,hn 32 (by decide),hn 64 (by decide),hn 160 (by decide)]
  rw [decodeSolcBytes32_total cd root {} false,solcReadNat_word_total cd (root+UInt256.ofNat 32)]
  rw [solcAdd_word]
  have hd := requestData_decode cd (delegatedAttestData cd root) false
  change decodeValue? requestDataABI cd.toList (root+calldataWord cd (root+UInt256.ofNat 32).toNat).toNat {} false = _ at hd
  rw [signatureAt_decode_cases cd (root+UInt256.ofNat 64) false,
    decodeSolcScalar_total cd (root+UInt256.ofNat 160) .address {} false rfl]
  have ha : decodeABIWord? (.elem .address) (calldataWord cd (root+UInt256.ofNat 160).toNat) =
      if (calldataWord cd (root+UInt256.ofNat 160).toNat).toNat < EVM.addressModulus then
        some (.address (AccountAddress.ofNat (calldataWord cd (root+UInt256.ofNat 160).toNat).toNat)) else none := rfl
  rw [ha]
  by_cases ho : (calldataWord cd (root+UInt256.ofNat 32).toNat).toNat ≤ solcMaxU64
  · rw [if_neg (by omega : ¬ solcMaxU64 < (calldataWord cd (root+UInt256.ofNat 32).toNat).toNat)]
    simp only [bind,Option.bind_some]
    rw [hd]
    by_cases hd : requestDataValid cd (delegatedAttestData cd root)
    · rw [if_pos hd]
      by_cases hs : signatureAtValid cd (root+UInt256.ofNat 64)
      · rw [if_pos hs]
        by_cases ha : (calldataWord cd (root+UInt256.ofNat 160).toNat).toNat < EVM.addressModulus
        · rw [if_pos ha,if_pos (show delegatedAttestFieldsValid cd root from ⟨ho,hd,hs,ha⟩)]
          rfl
        · rw [if_neg ha,if_neg (show ¬ delegatedAttestFieldsValid cd root from fun h => ha h.2.2.2)]
          rfl
      · rw [if_neg hs,if_neg (show ¬ delegatedAttestFieldsValid cd root from fun h => hs h.2.2.1)]
        rfl
    · rw [if_neg hd,if_neg (show ¬ delegatedAttestFieldsValid cd root from fun h => hd h.2.1)]
      rfl
  · rw [if_pos (by omega : solcMaxU64 < (calldataWord cd (root+UInt256.ofNat 32).toNat).toNat),
      if_neg (show ¬ delegatedAttestFieldsValid cd root from fun h => ho h.1)]
    rfl


theorem delegatedAttestRequest_decode (cd : ByteArray) (root : UInt256) :
    decodeValue? delegatedAttestABI cd.toList root.toNat {} false =
      if delegatedAttestRequestValid cd root then some (delegatedAttestRecord cd root).tuple else none := by
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq,Array.length_toList]; rfl
  have hs : solcSub cd.size root.toNat = (UInt256.sub (UInt256.ofNat cd.size) root).toNat := by
    unfold solcSub EVM.Word.ofNat
    rw [u256_ofNat_toNat]
    rfl
  rw [delegatedAttestABI,decodeValue?]
  simp only [show abiTupleHeadSize? [abiBytes32,requestDataABI,signatureABI,.elem .address] = some 192 by native_decide,
    show isDynamicABIType (.tuple [abiBytes32,requestDataABI,signatureABI,.elem .address]) = true by native_decide,
    show isMemory ({} : CalldataPlan) = true from rfl,
    show (List.range [abiBytes32,requestDataABI,signatureABI,.elem .address].length).map (fun i => child {} (.field i)) =
      [{},{},{},{}] by native_decide,
    Bool.not_false,Bool.true_or,Bool.true_and,Bool.not_true,Bool.false_eq_true,if_false,
    bind,Option.bind_some,pure,hlen,hs]
  by_cases hh : UInt256.slt (UInt256.sub (UInt256.ofNat cd.size) root) ⟨192⟩ = ⟨0⟩
  · have hc : solcSLT (UInt256.sub (UInt256.ofNat cd.size) root).toNat 192 = false :=
      (solcSLT_word_false _ (⟨192⟩ : UInt256)).mpr hh
    rw [hc]
    simp only [Bool.false_eq_true,if_false]
    have he := delegatedAttestFields_decode cd root
    simp only [delegatedAttestRequestValid,hh,true_and]
    cases hd : decodeFields? [abiBytes32,requestDataABI,signatureABI,.elem .address] cd.toList root.toNat 0 [{},{},{},{}] true <;>
      rw [hd] at he <;> exact he
  · have hc : solcSLT (UInt256.sub (UInt256.ofNat cd.size) root).toNat 192 = true := by
      cases hb : solcSLT (UInt256.sub (UInt256.ofNat cd.size) root).toNat 192
      · exact False.elim (hh ((solcSLT_word_false _ (⟨192⟩ : UInt256)).mp hb))
      · rfl
    rw [hc]
    simp only [if_true]
    rw [if_neg (fun h => hh h.1)]

def delegatedAttestValid (cd : ByteArray) : Prop :=
  (calldataWord cd 4).toNat ≤ solcMaxU64 ∧ delegatedAttestRequestValid cd (attestRoot cd)
instance (cd : ByteArray) : Decidable (delegatedAttestValid cd) := inferInstanceAs (Decidable (_ ∧ _))

theorem decodeDelegatedAttest {cd : ByteArray} (name : Ident) (table : List (Nat × List CalldataPlan))
    (h4 : 4 ≤ cd.size) (hhead : solcSLT (solcSub cd.size 4) 32 = false)
    (hplans : ((table.find? (fun entry => entry.1 == (bytesToWord (cd.toList.take 4)).toNat)).map Prod.snd).getD [] = []) :
    decodeCalldataWithMode (.solc08Calldata table) [name] [delegatedAttestABI] cd =
      if delegatedAttestValid cd then some ((∅ : Store).insert name (delegatedAttestRecord cd (attestRoot cd)).tuple) else none := by
  rw [decodeCalldataSolc08,if_neg (by omega : ¬ cd.size < 4)]
  simp only [decodeArgs?,List.isEmpty_cons,Bool.false_eq_true,if_false,
    show abiTupleHeadSize? [delegatedAttestABI] = some 32 by native_decide,
    bind,Option.bind_some,hhead,hplans]
  simp only [decodeFields?,show stride? delegatedAttestABI = some 32 by native_decide,
    show isDynamicABIType delegatedAttestABI = true by native_decide,
    if_true,if_false,List.headD_nil,List.tail_nil,retainFailure,
    show ({} : CalldataPlan).deferErrors.contains [] = false from rfl,
    Bool.false_eq_true,solcTailTarget?,Bool.not_true,show solcAdd 4 0 = 4 from rfl,
    bind,Option.bind_some,Bool.true_and,Bool.and_false,pure]
  have hread : solcReadNat cd.toList 4 = (calldataWord cd 4).toNat := solcReadNat_word_total cd (⟨4⟩ : UInt256)
  rw [hread]
  by_cases ho : (calldataWord cd 4).toNat ≤ solcMaxU64
  · rw [if_neg (by omega : ¬ solcMaxU64 < (calldataWord cd 4).toNat)]
    have hp : solcAdd 4 (calldataWord cd 4).toNat = (attestRoot cd).toNat := solcAdd_word ⟨4⟩ (calldataWord cd 4)
    simp only [hp,Option.bind_some]
    rw [delegatedAttestRequest_decode]
    by_cases hv : delegatedAttestRequestValid cd (attestRoot cd)
    · rw [if_pos hv,if_pos ⟨ho,hv⟩]
      rfl
    · rw [if_neg hv,if_neg (fun h => hv h.2)]
      rfl
  · rw [if_pos (by omega : solcMaxU64 < (calldataWord cd 4).toNat),if_neg (fun h => ho h.1)]
    rfl

end Benchmarks.EAS.EAS
