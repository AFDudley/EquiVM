import Benchmarks.EAS.EAS.SignatureArrayWords
import Benchmarks.EAS.EAS.CalldataArrayExtent
import Benchmarks.EAS.EAS.CalldataGuards
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: multiplying by a bounded literal gives the corresponding modular natural product.
theorem wordMul_nat (word : UInt256) (n : Nat) (hn : n<UInt256.size) :
    UInt256.mul word (UInt256.ofNat n) = UInt256.ofNat (n*word.toNat) := by
  apply u256_inj
  rw [u256_mul_toNat,ulit_toNat' _ hn]
  change (word.toNat*n)%UInt256.size = (n*word.toNat)%UInt256.size
  rw [Nat.mul_comm]

def signatureArrayHeaderValid (cd : ByteArray) (header : UInt256) : Prop :=
  (calldataWord cd header.toNat).toNat ≤ 2^64-1 ∧
  UInt256.gt ((header+UInt256.ofNat 32)+UInt256.mul (calldataWord cd header.toNat) (UInt256.ofNat 96))
    (UInt256.ofNat cd.size) = ⟨0⟩
instance (cd : ByteArray) (header : UInt256) : Decidable (signatureArrayHeaderValid cd header) :=
  inferInstanceAs (Decidable (_ ∧ _))

def decodeSignatureArray (cd : ByteArray) (header : UInt256) : Option (List SignatureRecord) :=
  if signatureArrayHeaderValid cd header then
    let ss := signatureRecords cd (header+UInt256.ofNat 32).toNat (calldataWord cd header.toNat).toNat
    if ∀ s∈ss,signatureClean s then some ss else none
  else none

theorem signatureArrayHeaderValid.extent {cd : ByteArray} {header : UInt256}
    (h : signatureArrayHeaderValid cd header) (hsize : cd.size < 2^255+4) :
    (header+UInt256.ofNat 32).toNat+96*(calldataWord cd header.toNat).toNat ≤ cd.size := by
  have hn := h.1
  apply calldataArrayExtent_stride hsize (by omega)
  simpa only [wordMul_nat _ 96 (by decide)] using h.2

theorem signatureArray_decode (cd : ByteArray) (header : UInt256) (hsize : cd.size < 2^255+4) :
    decodeValue? (.dynamicArray signatureABI) cd.toList header.toNat {} true =
      (decodeSignatureArray cd header).map (fun rs => Value.array (rs.map SignatureRecord.tuple)) := by
  let len := calldataWord cd header.toNat
  let offset := header+UInt256.ofNat 32
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq,Array.length_toList]; rfl
  have h32 : solcAdd header.toNat 32 = offset.toNat := solcAdd_word header (UInt256.ofNat 32)
  rw [decodeValue?,solcReadNat_word_total]
  simp only [show stride? signatureABI = some 96 by native_decide,
    show isDynamicABIType signatureABI = false from rfl,
    show isMemory ({} : CalldataPlan) = true from rfl,
    show (child ({} : CalldataPlan) .element).deferErrors.isEmpty = true from rfl,
    Bool.not_false,Bool.true_and,if_true,bind,Option.bind_some]
  by_cases hl : len.toNat ≤ 2^64-1
  · have hl' : ¬ solcMaxU64 < (calldataWord cd header.toNat).toNat := by change ¬ 18446744073709551615 < len.toNat; omega
    simp only [hl',decide_false,Bool.false_or,badExtent,Bool.not_true,Bool.false_and,Bool.true_and,Bool.false_eq_true,if_false,hlen,h32]
    have hshift : UInt256.mul len (UInt256.ofNat 96) = UInt256.ofNat (96*len.toNat) := wordMul_nat len 96 (by decide)
    have hs : solcAdd offset.toNat ((calldataWord cd header.toNat).toNat*96) =
        (offset+UInt256.mul len (UInt256.ofNat 96)).toNat := by
      rw [hshift]
      have hn : (UInt256.ofNat (96*len.toNat)).toNat = 96*len.toNat := ulit_toNat' _ (by change _ < 2^256; omega)
      have he := solcAdd_word offset (UInt256.ofNat (96*len.toNat))
      rw [hn] at he
      simpa only [Nat.mul_comm,len] using he
    rw [hs]
    have hmod : cd.size % EVM.wordModulus = (UInt256.ofNat cd.size).toNat := rfl
    rw [hmod]
    by_cases he : UInt256.gt (offset+UInt256.mul len (UInt256.ofNat 96)) (UInt256.ofNat cd.size) = ⟨0⟩
    · have he' := ugt_eq_zero_to_le he
      simp only [show ¬ (UInt256.ofNat cd.size).toNat < (offset+UInt256.mul len (UInt256.ofNat 96)).toNat by omega,
        decide_false,if_false]
      have hh : signatureArrayHeaderValid cd header := ⟨hl,he⟩
      have hc := hh.extent hsize
      rw [show (calldataWord cd header.toNat).toNat*96/32 = 3*(calldataWord cd header.toNat).toNat by omega,
        signatureArrayWords_decode hc (by change cd.size < 2^256; omega),decodeSignatureArray,if_pos hh]
      simp only [Bool.false_eq_true,if_false,signatureABI]
      by_cases hclean : ∀ s∈signatureRecords cd (header+UInt256.ofNat 32).toNat (calldataWord cd header.toNat).toNat,signatureClean s
      · rw [if_pos hclean,if_pos hclean]; rfl
      · rw [if_neg hclean,if_neg hclean]; rfl
    · have he' : (UInt256.ofNat cd.size).toNat < (offset+UInt256.mul len (UInt256.ofNat 96)).toNat := by
        have h := (word_gt_zero _ _).not.mp he
        omega
      simp only [he',decide_true,if_true]
      rw [decodeSignatureArray,if_neg (fun (h : signatureArrayHeaderValid cd header) => he h.2)]
      rfl
  · have hl' : solcMaxU64 < (calldataWord cd header.toNat).toNat := by change 18446744073709551615 < len.toNat; omega
    simp only [hl',decide_true,Bool.true_or,if_true]
    rw [decodeSignatureArray,if_neg (fun h => hl h.1)]
    rfl


structure SignatureArrayCalldataView (cd : ByteArray) (offset : UInt256) (rs : List SignatureRecord) : Prop where
  extent : offset.toNat+96*rs.length ≤ cd.size
  signatures : ∀ i (hi : i < rs.length), signatureRecord cd (offset.toNat+96*i) = rs[i]
  clean : ∀ s∈rs,signatureClean s

theorem decodeSignatureArray_facts {cd : ByteArray} {header : UInt256} {ss : List SignatureRecord}
    (hsize : cd.size < 2^255+4) (h : decodeSignatureArray cd header = some ss) :
    signatureArrayHeaderValid cd header ∧ ss.length = (calldataWord cd header.toNat).toNat ∧
    SignatureArrayCalldataView cd (header+UInt256.ofNat 32) ss := by
  unfold decodeSignatureArray at h
  split at h
  · rename_i hh
    dsimp only at h
    split at h
    · rename_i hc
      obtain ⟨rfl⟩ := Option.some.inj h
      exact ⟨hh,signatureRecords_length _ _ _,
        by simpa only [signatureRecords_length] using hh.extent hsize,
        fun i hi => (signatureRecords_get _ _ _ i hi).symm,hc⟩
    · contradiction
  · contradiction

end Benchmarks.EAS.EAS
