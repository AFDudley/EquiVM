import Benchmarks.EAS.EAS.CalldataBytes
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS

-- GENERALIZES solcSLT_sub4_of_check to arbitrary word operands.
theorem solcSLT_word (a b : UInt256) :
    solcSLT a.toNat b.toNat = UInt256.sltBool a b := by
  unfold solcSLT EVM.Word.ofNat
  rw [u256_ofNat_toNat,u256_ofNat_toNat,← sltBool_signed]

-- LIBRARY CANDIDATE: the ABI signed-check flag agrees with the EVM zero branch.
theorem solcSLT_word_false (a b : UInt256) :
    solcSLT a.toNat b.toNat = false ↔ UInt256.slt a b = ⟨0⟩ := by
  rw [solcSLT_word]
  unfold UInt256.slt
  cases UInt256.sltBool a b <;> decide

-- LIBRARY CANDIDATE: the negated ABI signed-check flag agrees with the EVM guard.
theorem solcSLT_word_true (a b : UInt256) :
    solcSLT a.toNat b.toNat = true ↔ UInt256.isZero (UInt256.slt a b) = ⟨0⟩ := by
  rw [solcSLT_word]
  unfold UInt256.slt
  cases UInt256.sltBool a b <;> decide

-- LIBRARY CANDIDATE: the unsigned ABI end check agrees with GT's zero branch.
theorem word_gt_zero (a b : UInt256) :
    UInt256.gt a b = ⟨0⟩ ↔ a.toNat ≤ b.toNat :=
  ⟨ugt_eq_zero_to_le,ugt_zero⟩

-- LIBRARY CANDIDATE: wrapping ABI additions are EVM word additions.
theorem solcAdd_word (a b : UInt256) : solcAdd a.toNat b.toNat = (a+b).toNat :=
  (uadd_toNat a b).symm

theorem solcSub_word (a b : UInt256) : solcSub a.toNat b.toNat = (UInt256.sub a b).toNat := by
  unfold solcSub EVM.Word.ofNat
  rw [u256_ofNat_toNat,u256_ofNat_toNat]
  rfl

-- GENERALIZES decodeSolcString to arbitrary wrapping pointers, without requiring complete slices.
theorem decodeSolcBytes_total (cd : ByteArray) (start : UInt256) (plan : CalldataPlan) :
    decodeValue? .bytes cd.toList start.toNat plan false =
      if UInt256.isZero (UInt256.slt (start+⟨31⟩) (UInt256.ofNat cd.size)) = ⟨0⟩ ∧
          (calldataWord cd start.toNat).toNat ≤ solcMaxU64 ∧
          UInt256.gt ((start+calldataWord cd start.toNat)+⟨32⟩) (UInt256.ofNat cd.size) = ⟨0⟩ then
        some (.bytes (cd.readBytes (start.toNat+32) (calldataWord cd start.toNat).toNat))
      else none := by
  let len := calldataWord cd start.toNat
  have hsize : cd.toList.length = cd.size := by rw [byteArray_toList_eq,Array.length_toList]; rfl
  have h31 : solcAdd start.toNat 31 = (start+⟨31⟩).toNat := solcAdd_word start ⟨31⟩
  have h32 : solcAdd start.toNat 32 = (start+⟨32⟩).toNat := solcAdd_word start ⟨32⟩
  have hnext : solcAdd (solcAdd start.toNat 32) len.toNat = ((start+len)+⟨32⟩).toNat := by
    rw [h32,solcAdd_word]
    rw [u256_add_assoc,u256_add_comm (⟨32⟩ : UInt256),← u256_add_assoc]
  have hsign : solcSLT (solcAdd start.toNat 31) cd.size =
      solcSLT (start+⟨31⟩).toNat (UInt256.ofNat cd.size).toNat := by
    rw [h31]
    unfold solcSLT EVM.Word.ofNat
    simp only [u256_ofNat_toNat]
  have hmod : cd.size % EVM.wordModulus = (UInt256.ofNat cd.size).toNat := rfl
  rw [decodeValue?,solcReadNat_word_total]
  change (if decide (solcMaxU64 < len.toNat) || badExtent (isMemory plan) false cd.toList start.toNat len.toNat 1
    then none else _) = _
  simp only [badExtent,Bool.not_false,Bool.true_and,Bool.false_and,Bool.false_eq_true,if_false,
    Nat.mul_one,hsize,hnext,hmod,hsign]
  by_cases hh : UInt256.isZero (UInt256.slt (start+⟨31⟩) (UInt256.ofNat cd.size)) = ⟨0⟩
  · have hs := (solcSLT_word_true _ _).mpr hh
    rw [hs]
    by_cases hl : len.toNat ≤ solcMaxU64
    · have hn : ¬ solcMaxU64 < len.toNat := by omega
      simp only [hn,decide_false,Bool.not_true,Bool.false_or]
      by_cases he : UInt256.gt ((start+len)+⟨32⟩) (UInt256.ofNat cd.size) = ⟨0⟩
      · have he' := (word_gt_zero _ _).mp he
        simp only [show ¬ (UInt256.ofNat cd.size).toNat < ((start+len)+⟨32⟩).toNat by omega,
          decide_false,Bool.false_eq_true,if_false]
        rw [decodePaddedBytes cd start hl]
        rw [if_pos ⟨hh,hl,he⟩]
        rfl
      · have he' : (UInt256.ofNat cd.size).toNat < ((start+len)+⟨32⟩).toNat := by
          have := (word_gt_zero _ _).not.mp he
          omega
        simp only [he',decide_true,if_true]
        rw [if_neg (fun h => he h.2.2)]
    · have hn : solcMaxU64 < len.toNat := by omega
      simp only [hn,decide_true,Bool.true_or,if_true]
      rw [if_neg (fun h => hl h.2.1)]
  · have hs : solcSLT (start+⟨31⟩).toNat (UInt256.ofNat cd.size).toNat = false := by
      cases he : solcSLT (start+⟨31⟩).toNat (UInt256.ofNat cd.size).toNat
      · rfl
      · exact False.elim (hh ((solcSLT_word_true _ _).mp he))
    simp only [hs,Bool.not_false,Bool.true_or,Bool.or_true,if_true]
    rw [if_neg (fun h => hh h.1)]

end Benchmarks.EAS.EAS
