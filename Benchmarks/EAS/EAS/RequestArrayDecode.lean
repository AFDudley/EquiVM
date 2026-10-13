import Benchmarks.EAS.EAS.RequestArrayElements
import Benchmarks.EAS.EAS.CalldataArrayExtent
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def requestArrayHeaderValid (cd : ByteArray) (header : UInt256) : Prop :=
  (calldataWord cd header.toNat).toNat ≤ 2^64-1 ∧
  UInt256.gt ((header+UInt256.ofNat 32)+UInt256.shiftLeft (calldataWord cd header.toNat) (UInt256.ofNat 5))
    (UInt256.ofNat cd.size) = ⟨0⟩
instance (cd : ByteArray) (header : UInt256) : Decidable (requestArrayHeaderValid cd header) :=
  inferInstanceAs (Decidable (_ ∧ _))

def decodeRequestArray (cd : ByteArray) (header : UInt256) : Option (List AttestationRequestRecord) :=
  if requestArrayHeaderValid cd header then
    decodeRequestElements cd (header+UInt256.ofNat 32) 0 (calldataWord cd header.toNat).toNat else none

theorem requestArray_decode (cd : ByteArray) (header : UInt256) (hsize : cd.size < 2^255+4) :
    decodeValue? (.dynamicArray requestDataABI) cd.toList header.toNat {} true =
      (decodeRequestArray cd header).map (fun rs => Value.array (rs.map AttestationRequestRecord.tuple)) := by
  let len := calldataWord cd header.toNat
  let offset := header+UInt256.ofNat 32
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq,Array.length_toList]; rfl
  have h32 : solcAdd header.toNat 32 = offset.toNat := solcAdd_word header (UInt256.ofNat 32)
  rw [decodeValue?,solcReadNat_word_total]
  simp only [show stride? requestDataABI = some 32 by native_decide,
    show isDynamicABIType requestDataABI = true by native_decide,
    show isMemory ({} : CalldataPlan) = true from rfl,
    Bool.not_true,Bool.false_and,Bool.false_eq_true,if_false,bind,Option.bind_some]
  by_cases hl : len.toNat ≤ 2^64-1
  · have hl' : ¬ solcMaxU64 < (calldataWord cd header.toNat).toNat := by change ¬ 18446744073709551615 < len.toNat; omega
    simp only [hl',decide_false,Bool.false_or,badExtent,Bool.not_true,Bool.false_and,Bool.true_and,Bool.false_eq_true,if_false,hlen,h32]
    have hshift : UInt256.shiftLeft len (UInt256.ofNat 5) = UInt256.ofNat (32*len.toNat) := by
      simpa only [u256_ofNat_toNat] using shiftLeft5_ofNat_eq (n := len.toNat) (by change _ < 2^256; omega)
    have hs : solcAdd offset.toNat ((calldataWord cd header.toNat).toNat*32) =
        (offset+UInt256.shiftLeft len (UInt256.ofNat 5)).toNat := by
      rw [hshift]
      have hn : (UInt256.ofNat (32*len.toNat)).toNat = 32*len.toNat := ulit_toNat' _ (by change _ < 2^256; omega)
      have he := solcAdd_word offset (UInt256.ofNat (32*len.toNat))
      rw [hn] at he
      simpa only [Nat.mul_comm,len] using he
    rw [hs]
    have hmod : cd.size % EVM.wordModulus = (UInt256.ofNat cd.size).toNat := rfl
    rw [hmod]
    by_cases he : UInt256.gt (offset+UInt256.shiftLeft len (UInt256.ofNat 5)) (UInt256.ofNat cd.size) = ⟨0⟩
    · have he' := ugt_eq_zero_to_le he
      simp only [show ¬ (UInt256.ofNat cd.size).toNat < (offset+UInt256.shiftLeft len (UInt256.ofNat 5)).toNat by omega,
        decide_false,if_false]
      have hh : requestArrayHeaderValid cd header := ⟨hl,he⟩
      rw [decodeRequestArray,if_pos hh]
      have hb := calldataArrayExtent_complete hsize hl he
      have hd := requestArrayElements_decode cd offset 0 len.toNat (by change _ < 2^256; dsimp only [offset] at ⊢; omega)
      simp only [Nat.mul_zero,Nat.zero_add] at hd
      rw [hd]
      cases decodeRequestElements cd offset 0 len.toNat <;> rfl
    · have he' : (UInt256.ofNat cd.size).toNat < (offset+UInt256.shiftLeft len (UInt256.ofNat 5)).toNat := by
        have h := (word_gt_zero _ _).not.mp he
        omega
      simp only [he',decide_true,if_true]
      rw [decodeRequestArray,if_neg (fun (h : requestArrayHeaderValid cd header) => he h.2)]
      rfl
  · have hl' : solcMaxU64 < (calldataWord cd header.toNat).toNat := by change 18446744073709551615 < len.toNat; omega
    simp only [hl',decide_true,Bool.true_or,if_true]
    rw [decodeRequestArray,if_neg (fun h => hl h.1)]
    rfl

theorem decodeRequestArray_facts {cd : ByteArray} {header : UInt256} {rs : List AttestationRequestRecord}
    (hsize : cd.size < 2^255+4) (h : decodeRequestArray cd header = some rs) :
    requestArrayHeaderValid cd header ∧ rs.length = (calldataWord cd header.toNat).toNat ∧
    RequestArrayCalldataView cd (header+UInt256.ofNat 32) rs := by
  unfold decodeRequestArray at h
  by_cases hh : requestArrayHeaderValid cd header
  · rw [if_pos hh] at h
    obtain ⟨hl,hr⟩ := decodeRequestElements_facts h
    refine ⟨hh,hl,?_,?_⟩
    · rw [hl]
      exact calldataArrayExtent_complete hsize hh.1 hh.2
    · intro i hi
      have hf := hr i hi
      simp only [Nat.zero_add] at hf
      exact ⟨hf.1.1,hf.1.2,hf.2⟩
  · rw [if_neg hh] at h
    contradiction

end Benchmarks.EAS.EAS
