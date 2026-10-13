import Benchmarks.EAS.EAS.SignatureDecode
import Benchmarks.EAS.EAS.VerifyRevokeSource
import Benchmarks.EAS.EAS.RevocationArrayWords
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def delegatedRevokeABI : ABIType := .tuple [abiBytes32,revocationDataABI,signatureABI,.elem .address]
def delegatedRevokeRecord (cd : ByteArray) (start : Nat) : DelegatedRevocationRecord :=
  ⟨calldataWord cd start,revocationDataRecord cd (start+32),signatureRecord cd (start+96),
    AccountAddress.ofNat (calldataWord cd (start+192)).toNat⟩
def delegatedRevokeClean (cd : ByteArray) (start : Nat) : Prop :=
  signatureClean (signatureRecord cd (start+96)) ∧ (calldataWord cd (start+192)).toNat < EVM.addressModulus
instance (cd : ByteArray) (start : Nat) : Decidable (delegatedRevokeClean cd start) := inferInstanceAs (Decidable (_ ∧ _))

theorem decodeDelegatedRevokeTuple {bytes : List UInt8} {start : Nat}
    (hlen : ∀ off, off ≤ 192 → ((bytes.drop (start+off)).take 32).length = 32) :
    decodeABIValue? delegatedRevokeABI bytes start = (do
      let sv ← decodeABIWord? abiUInt8 (bytesToWord ((bytes.drop (start+96)).take 32))
      let a ← decodeABIWord? (.elem .address) (bytesToWord ((bytes.drop (start+192)).take 32))
      some (.tuple [.fixedBytes abiBytes32Width ((bytes.drop start).take 32),
        .tuple [.fixedBytes abiBytes32Width ((bytes.drop (start+32)).take 32),
          .int (Int.ofNat (bytesToWord ((bytes.drop (start+64)).take 32)).toNat)],
        .tuple [sv,.fixedBytes abiBytes32Width ((bytes.drop (start+128)).take 32),
          .fixedBytes abiBytes32Width ((bytes.drop (start+160)).take 32)],a],start+224)) := by
  rw [delegatedRevokeABI,decodeABIValue?]
  simp only [bind,show abiTupleHeadSize? [abiBytes32,revocationDataABI,signatureABI,.elem .address] = some 224 by native_decide,Option.bind]
  simp only [decodeABIValues?,show isDynamicABIType abiBytes32 = false from rfl,
    show isDynamicABIType revocationDataABI = false from rfl,show isDynamicABIType signatureABI = false from rfl,
    show isDynamicABIType (.elem .address) = false from rfl,
    show staticABIEncodedSize? abiBytes32 = some 32 from rfl,
    show staticABIEncodedSize? revocationDataABI = some 64 from rfl,
    show staticABIEncodedSize? signatureABI = some 96 from rfl,
    show staticABIEncodedSize? (.elem .address) = some 32 from rfl,
    Bool.false_eq_true,if_false,bind,Option.bind,Nat.add_zero,Nat.zero_add]
  simp only [revocationDataABI,Nat.add_assoc,Nat.reduceAdd]
  rw [decodeABIValue_bytes32_ok (by simpa only [Nat.add_zero] using hlen 0 (by decide)),
    decodeBytes32UIntTuple (hlen 32 (by decide)) (by simpa only [Nat.add_assoc,Nat.reduceAdd] using hlen 64 (by decide)),
    decodeSignatureTuple (hlen 96 (by decide)) (by simpa only [Nat.add_assoc,Nat.reduceAdd] using hlen 128 (by decide))
      (by simpa only [Nat.add_assoc,Nat.reduceAdd] using hlen 160 (by decide)),
    decodeABIValue_scalarWord_eq (ty := .elem .address) (by rfl)]
  simp only [decodeScalarWord?,readWord?,readBytes?,hlen 192 (by decide),if_true,bind,Option.bind,pure,Nat.add_assoc,Nat.reduceAdd]
  cases decodeABIWord? abiUInt8 (bytesToWord ((bytes.drop (start+96)).take 32)) <;>
    cases decodeABIWord? (.elem .address) (bytesToWord ((bytes.drop (start+192)).take 32)) <;>
    simp only [Option.bind_some,Option.bind_none,Option.map_some,Option.map_none,if_true,
      Nat.max_eq_left (by omega : start+32 ≤ start+224),Nat.max_eq_left (by omega : start+96 ≤ start+224),
      Nat.max_eq_left (by omega : start+192 ≤ start+224),Nat.max_self]


theorem delegatedRevokeWords_decode {cd : ByteArray} {start : Nat}
    (hb : start+224 ≤ cd.size) (hsize : cd.size < UInt256.size) :
    decodeABIValue? delegatedRevokeABI (solcReadWords cd.toList start 7) 0 =
      if delegatedRevokeClean cd start then some ((delegatedRevokeRecord cd start).tuple,224) else none := by
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq,Array.length_toList]; rfl
  rw [solcReadWords_slice (by rw [hlen]; omega) (by rw [hlen]; exact hsize)]
  have hw (off : Nat) (ho : off ≤ 192) := calldataSlice_word (off := off) hb (by omega : off+32 ≤ 224)
  rw [decodeDelegatedRevokeTuple (by
    intro off ho
    simpa only [Nat.zero_add,hw off ho,word_toBytesBE_length_32])]
  simp only [Nat.zero_add,Nat.reduceMul]
  rw [hw 0 (by decide),hw 32 (by decide),hw 64 (by decide),hw 96 (by decide),
    hw 128 (by decide),hw 160 (by decide),hw 192 (by decide)]
  simp only [bytesToWord_toBytesBE,Nat.add_zero]
  rw [show abiUInt8 = .elem (.int (.uint ⟨8,by decide⟩)) from rfl,
    decodeUIntWord_mask ⟨8,by decide⟩ _ (UInt256.ofNat 255) rfl (by decide)]
  simp only [decodeABIWord?]
  by_cases hv : calldataWord cd (start+96) = UInt256.land (calldataWord cd (start+96)) (UInt256.ofNat 255)
  · rw [if_pos hv]
    by_cases ha : (calldataWord cd (start+192)).toNat < EVM.addressModulus
    · rw [if_pos (show (↑(calldataWord cd (start+192)).val : Nat) < EVM.addressModulus from ha),
        if_pos (show delegatedRevokeClean cd start from ⟨hv,ha⟩)]
      simp only [bind,Option.bind,delegatedRevokeRecord,DelegatedRevocationRecord.tuple,
        RevocationRequestRecord.tuple,SignatureRecord.tuple,revocationDataRecord,signatureRecord,
        Nat.add_assoc,Nat.reduceAdd,wordBytes32Value]
      rfl
    · rw [if_neg (show ¬ (↑(calldataWord cd (start+192)).val : Nat) < EVM.addressModulus from ha),
        if_neg (show ¬ delegatedRevokeClean cd start from fun h => ha h.2)]
      rfl
  · rw [if_neg hv,if_neg (show ¬ delegatedRevokeClean cd start from fun h => hv h.1)]
    rfl

theorem decodeDelegatedRevoke {cd : ByteArray} (name : Ident) (table : List (Nat × List CalldataPlan))
    (hsize : cd.size < UInt256.size) (h228 : 228 ≤ cd.size)
    (hhead : solcSLT (solcSub cd.size 4) 224 = false)
    (hplans : ((table.find? (fun entry => entry.1 == (bytesToWord (cd.toList.take 4)).toNat)).map Prod.snd).getD [] = []) :
    decodeCalldataWithMode (.solc08Calldata table) [name] [delegatedRevokeABI] cd =
      if delegatedRevokeClean cd 4 then some ((∅ : Store).insert name (delegatedRevokeRecord cd 4).tuple) else none := by
  rw [decodeCalldataSolc08,if_neg (by omega : ¬ cd.size < 4)]
  simp only [bind,decodeArgs?,List.isEmpty_cons,Bool.false_eq_true,if_false,
    show abiTupleHeadSize? [delegatedRevokeABI] = some 224 by native_decide,bind,Option.bind,hhead,hplans]
  simp only [bind,decodeFields?,show stride? delegatedRevokeABI = some 224 from rfl,
    show isDynamicABIType delegatedRevokeABI = false from rfl,List.headD_nil,List.tail_nil,retainFailure,
    show ({} : CalldataPlan).deferErrors.contains [] = false from rfl,
    Bool.false_eq_true,if_false,Bool.false_and,show solcAdd 4 0 = 4 from rfl,Option.bind,pure]
  rw [delegatedRevokeABI,decodeValue?]
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq,Array.length_toList]; rfl
  simp only [bind,show abiTupleHeadSize? [abiBytes32,revocationDataABI,signatureABI,.elem .address] = some 224 by native_decide,
    show isDynamicABIType (.tuple [abiBytes32,revocationDataABI,signatureABI,.elem .address]) = false from rfl,
    Bool.not_false,Bool.true_or,Bool.true_and,Option.bind,hlen,hhead,if_false,if_true]
  rw [show 224/32 = 7 from rfl,← delegatedRevokeABI,delegatedRevokeWords_decode (by omega) hsize]
  by_cases hc : delegatedRevokeClean cd 4 <;>
    simp only [hc,if_true,if_false,bind,Option.map_some,Option.map_none,Option.bind,decodeCalldata.insertValues,Bool.false_eq_true,if_false]

end Benchmarks.EAS.EAS
