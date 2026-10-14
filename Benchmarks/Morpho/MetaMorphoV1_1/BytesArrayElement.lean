import Benchmarks.Morpho.MetaMorphoV1_1.BytesArrayCalldata
import Benchmarks.Morpho.MetaMorphoV1_1.CalldataReferenceBytes

/-! Each bytes-array access retains its signed offset check and materializing payload check. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false
set_option maxRecDepth 2000

def bytesTailValid (cd : ByteArray) (head : UInt256) : Prop :=
  (calldataWord cd head.toNat).toNat ≤ solcMaxU64 ∧
    ((head + ⟨32⟩) + calldataWord cd head.toNat).toNat ≤ (UInt256.ofNat cd.size).toNat

instance (cd : ByteArray) (head : UInt256) : Decidable (bytesTailValid cd head) :=
  inferInstanceAs (Decidable (_ ∧ _))

def bytesTailData (cd : ByteArray) (head : UInt256) : ByteArray :=
  cd.readBytes (head.toNat + 32) (calldataWord cd head.toNat).toNat

-- LIBRARY CANDIDATE: materialized bytes after a direct calldata-reference access.
theorem decodeMaterializedBytesTail (cd : ByteArray) (head : UInt256) (plan : CalldataPlan)
    (hm : isMemory plan = true) :
    decodeValue? .bytes cd.toList head.toNat plan true =
      if bytesTailValid cd head then some (.bytes (bytesTailData cd head)) else none := by
  have hsize : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have h32 : solcAdd head.toNat 32 = (head + ⟨32⟩).toNat := solcAdd_word head ⟨32⟩
  rw [decodeValue?, solcReadNat_word_total]
  simp only [badExtent, hm, Bool.not_true, Bool.false_and, Bool.and_false,
    Bool.false_or, Bool.false_eq_true, if_false, Nat.mul_one, hsize, h32, solcAdd_word]
  change (if (decide (solcMaxU64 < (calldataWord cd head.toNat).toNat) ||
    decide ((UInt256.ofNat cd.size).toNat <
      ((head + ⟨32⟩) + calldataWord cd head.toNat).toNat)) = true then none else _) = _
  by_cases hc : bytesTailValid cd head
  · have hn := Nat.not_lt.mpr hc.1
    have he := Nat.not_lt.mpr hc.2
    rw [if_pos hc]
    simp only [hn, he, decide_false, Bool.false_or, Bool.false_eq_true, if_false]
    rw [decodeSolcPaddedBytes cd head hc.1]
    rfl
  · rw [if_neg hc]
    have hb : solcMaxU64 < (calldataWord cd head.toNat).toNat ∨
        (UInt256.ofNat cd.size).toNat <
          ((head + ⟨32⟩) + calldataWord cd head.toNat).toNat := by
      change ¬ (_ ∧ _) at hc
      omega
    rcases hb with hl | he
    · simp only [hl, decide_true, Bool.true_or, if_true]
    · simp only [he, decide_true, Bool.or_true, if_true]

-- LIBRARY CANDIDATE: a direct bytes tail uses the EVM's signed relative-offset check.
theorem solcBytesTailTarget (cd : ByteArray) (base entry : UInt256) :
    solcTailTarget? true .bytes cd.toList base.toNat entry.toNat =
      if UInt256.slt (calldataWord cd entry.toNat)
          ((UInt256.ofNat cd.size - base) - ⟨31⟩) = ⟨0⟩ then none
      else some (base + calldataWord cd entry.toNat).toNat := by
  have hsize : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hsub : solcSub (solcSub cd.size base.toNat) 31 =
      ((UInt256.ofNat cd.size - base) - ⟨31⟩).toNat := by
    simp only [solcSub, EVM.Word.ofNat, u256_ofNat_toNat]
    rfl
  simp only [solcTailTarget?, solcReadNat_word_total, tailSize?, bind, Option.bind,
    if_true, hsize, show solcSub 32 1 = 31 from rfl, hsub, solcAdd_word]
  by_cases hs : UInt256.slt (calldataWord cd entry.toNat)
      ((UInt256.ofNat cd.size - base) - ⟨31⟩) = ⟨0⟩
  · rw [(solcSLT_word_false _ _).mpr hs, if_pos hs]
    rfl
  · have ht : solcSLT (calldataWord cd entry.toNat).toNat
        ((UInt256.ofNat cd.size - base) - ⟨31⟩).toNat = true := by
      cases he : solcSLT (calldataWord cd entry.toNat).toNat
          ((UInt256.ofNat cd.size - base) - ⟨31⟩).toNat
      · exact False.elim (hs ((solcSLT_word_false _ _).mp he))
      · rfl
    rw [ht, if_neg hs]
    rfl

def bytesArrayRelative (cd : ByteArray) (base : UInt256) (i : Nat) : UInt256 :=
  calldataWord cd (base + UInt256.ofNat (32 * i)).toNat

def bytesArrayHead (cd : ByteArray) (base : UInt256) (i : Nat) : UInt256 :=
  base + bytesArrayRelative cd base i

def bytesArrayAccessValid (cd : ByteArray) (base : UInt256) (i : Nat) : Prop :=
  UInt256.slt (bytesArrayRelative cd base i)
      ((UInt256.ofNat cd.size - base) - ⟨31⟩) ≠ ⟨0⟩ ∧
    bytesTailValid cd (bytesArrayHead cd base i)

instance (cd : ByteArray) (base : UInt256) (i : Nat) :
    Decidable (bytesArrayAccessValid cd base i) := inferInstanceAs (Decidable (_ ∧ _))

theorem retainedCalldataBytesElement (cd : ByteArray) (base : UInt256) (i : Nat)
    (hi : 32 * i < UInt256.size) :
    retainedCalldataElement .bytes multicallCalldataPlan cd.toList base.toNat 32 i =
      if bytesArrayAccessValid cd base i then
        .bytes (bytesTailData cd (bytesArrayHead cd base i)) else decodeFailure := by
  have hiw : solcAdd base.toNat (32 * i) = (base + UInt256.ofNat (32 * i)).toNat := by
    rw [← UInt256.toNat_ofNat_of_lt hi, solcAdd_word, u256_ofNat_toNat]
  simp only [retainedCalldataElement, isDynamicABIType, if_true,
    show isMemory multicallCalldataPlan = false from rfl, Bool.not_false, Bool.and_self, hiw]
  rw [solcBytesTailTarget]
  change ((Option.bind
      (if UInt256.slt (bytesArrayRelative cd base i)
          ((UInt256.ofNat cd.size - base) - (⟨31⟩ : UInt256)) = (⟨0⟩ : UInt256) then none
        else some (bytesArrayHead cd base i).toNat)
      (fun target ↦ decodeValue? .bytes cd.toList target
        (child multicallCalldataPlan .element) true)).getD decodeFailure) = _
  by_cases ht : UInt256.slt (bytesArrayRelative cd base i)
      ((UInt256.ofNat cd.size - base) - ⟨31⟩) = ⟨0⟩
  · rw [if_pos ht, if_neg (fun hc ↦ hc.1 ht)]
    rfl
  · rw [if_neg ht]
    simp only [bind, Option.bind_some]
    rw [decodeMaterializedBytesTail _ _ _ rfl]
    by_cases hp : bytesTailValid cd (bytesArrayHead cd base i)
    · rw [if_pos hp, if_pos ⟨ht, hp⟩]
      rfl
    · rw [if_neg hp, if_neg (fun hc ↦ hp hc.2)]
      rfl

theorem bytesTailData_size (cd : ByteArray) (head : UInt256) :
    (bytesTailData cd head).size = (calldataWord cd head.toNat).toNat :=
  readBytes_padded_size _ _ _

end Benchmarks.Morpho.MetaMorphoV1_1
