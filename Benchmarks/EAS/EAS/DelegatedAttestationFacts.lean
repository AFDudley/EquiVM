import Benchmarks.EAS.EAS.DelegatedAttestationElements
import Benchmarks.EAS.EAS.SignatureArrayReferenceAccess
import Benchmarks.EAS.EAS.CalldataPayload
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: signed greater-than is reversed signed less-than.
theorem word_sgt_eq_slt (a b : UInt256) : UInt256.sgt a b=UInt256.slt b a := by
  unfold UInt256.sgt UInt256.slt UInt256.sgtBool UInt256.sltBool
  by_cases ha : 2^255 ≤ a.toNat <;> by_cases hb : 2^255 ≤ b.toNat <;>
    simp only [ha,hb,if_true,if_false]


theorem delegatedAttestationRequestAccess (cd : ByteArray) (root : UInt256) :
    requestArrayAccessValid cd root ↔ delegatedAttestationArrayReferenceValid cd root 32 ∧
      referencedArrayHeadValid cd (delegatedBatchArray cd root 32) 32 := by
  have hs := wordShiftLeft_nat (calldataWord cd (delegatedBatchArray cd root 32).toNat) 5 (by decide)
  simp only [show 2^5=32 from rfl] at hs
  unfold requestArrayAccessValid referencedArrayHeadValid
  change (_ ∧ _ ∧ UInt256.sgt (UInt256.ofNat 32+delegatedBatchArray cd root 32)
    (UInt256.ofNat cd.size-UInt256.shiftLeft (calldataWord cd (delegatedBatchArray cd root 32).toNat) (UInt256.ofNat 5))=⟨0⟩) ↔ _
  rw [hs,u256_add_comm (UInt256.ofNat 32),Nat.mul_comm 32,word_sgt_eq_slt]
  rfl

theorem delegatedAttestationSignatureAccess (cd : ByteArray) (root : UInt256) :
    signatureArrayReferenceAccessValid cd root ↔ delegatedAttestationArrayReferenceValid cd root 64 ∧
      referencedArrayHeadValid cd (delegatedBatchArray cd root 64) 96 := by
  unfold signatureArrayReferenceAccessValid referencedArrayHeadValid
  rw [wordMul_nat _ 96 (by decide),u256_add_comm (UInt256.ofNat 32),Nat.mul_comm 96,word_sgt_eq_slt]
  rfl

-- Only nonempty arrays are traversed; their readable length bounds every index.
theorem referencedArrayNonempty_span {cd : ByteArray} {header : UInt256} {stride : Nat}
    (hsize : cd.size < 2^255) (hstride : stride ≤ 96)
    (hh : referencedArrayHeadValid cd header stride) (hne : 0 < (calldataWord cd header.toNat).toNat) :
    (header+UInt256.ofNat 32).toNat+stride*(calldataWord cd header.toNat).toNat < UInt256.size := by
  have hr : header.toNat < cd.size := by
    by_contra hn
    have hz := Benchmarks.EAS.EAS.calldataWord_zero_of_ge cd header.toNat (by omega)
    rw [hz] at hne
    contradiction
  have hs : (header+UInt256.ofNat 32).toNat=header.toNat+32 := uadd_word_ofNat_toNat _ _ (by change _<2^256;omega)
  have hprod := Nat.mul_le_mul_right (calldataWord cd header.toNat).toNat hstride
  rw [hs]
  have hl := hh.1
  change _<2^256
  omega

theorem delegatedAttestationAddress_ne_failure (cd : ByteArray) (root : UInt256) :
    delegatedAttestationAddressValue cd root ≠ decodeFailure ↔ delegatedBatchAddressClean cd root := by
  by_cases h : delegatedBatchAddressClean cd root <;>
    simp [delegatedAttestationAddressValue,h,decodeFailure]

theorem delegatedAttestationDatum_ne_failure (cd : ByteArray) (offset : UInt256) (i : Nat) :
    delegatedAttestationDatum cd offset i ≠ decodeFailure ↔ delegatedAttestationDataValid cd offset i := by
  by_cases h : delegatedAttestationDataValid cd offset i <;>
    simp [delegatedAttestationDatum,h,AttestationRequestRecord.tuple,decodeFailure]

theorem delegatedAttestationSignature_ne_failure (cd : ByteArray) (offset : UInt256) (i : Nat) :
    delegatedAttestationSignature cd offset i ≠ decodeFailure ↔ signatureAtValid cd (UInt256.ofNat (offset.toNat+96*i)) := by
  by_cases h : signatureAtValid cd (UInt256.ofNat (offset.toNat+96*i)) <;>
    simp [delegatedAttestationSignature,h,SignatureRecord.tuple,decodeFailure]

end Benchmarks.EAS.EAS
