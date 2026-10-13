import Benchmarks.EAS.EAS.RecordMemory
import Benchmarks.EAS.EAS.PackedShift
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem AttestationMemoryView.uidFields {mem : ByteArray} {src dataPtr : UInt256} {a : AttestationRecord}
    (h : AttestationMemoryView mem src dataPtr a) :
    memLoad (src+UInt256.ofNat 32) mem = a.schema ∧
    UInt256.shiftLeft (memLoad (src+UInt256.ofNat 192) mem) (UInt256.ofNat 96) =
      UInt256.shiftLeft (UInt256.ofNat a.recipient.val) (UInt256.ofNat 96) ∧
    UInt256.shiftLeft (memLoad (src+UInt256.ofNat 224) mem) (UInt256.ofNat 96) =
      UInt256.shiftLeft (UInt256.ofNat a.attester.val) (UInt256.ofNat 96) ∧
    UInt256.shiftLeft (memLoad (src+UInt256.ofNat 64) mem) (UInt256.ofNat 192) =
      UInt256.shiftLeft a.time (UInt256.ofNat 192) ∧
    UInt256.shiftLeft (memLoad (src+UInt256.ofNat 96) mem) (UInt256.ofNat 192) =
      UInt256.shiftLeft a.expirationTime (UInt256.ofNat 192) ∧
    UInt256.isZero (UInt256.isZero (memLoad (src+UInt256.ofNat 256) mem)) = a.revocable.toUInt256 ∧
    memLoad (src+UInt256.ofNat 160) mem = a.refUID := by
  have hf := h.fields
  simp only [attestationEncodeHeadWords,attestationEncodeFirstWords,attestationEncodeLastWords,
    AttestationRecord.words,List.cons_append,List.nil_append,List.cons.injEq,and_true] at hf
  obtain ⟨_,hs,ht,he,_,href,hr,ha,hb⟩ := hf
  refine ⟨hs,?_,?_,?_,?_,hb,href⟩
  · have hv := congrArg (fun w => UInt256.shiftLeft w (UInt256.ofNat 96)) hr
    exact (shiftLeft_lowMask (memLoad (src+UInt256.ofNat 192) mem) 96 (by decide)).symm.trans hv
  · have hv := congrArg (fun w => UInt256.shiftLeft w (UInt256.ofNat 96)) ha
    exact (shiftLeft_lowMask (memLoad (src+UInt256.ofNat 224) mem) 96 (by decide)).symm.trans hv
  · have hv := congrArg (fun w => UInt256.shiftLeft w (UInt256.ofNat 192)) ht
    exact (shiftLeft_lowMask (memLoad (src+UInt256.ofNat 64) mem) 192 (by decide)).symm.trans hv
  · have hv := congrArg (fun w => UInt256.shiftLeft w (UInt256.ofNat 192)) he
    exact (shiftLeft_lowMask (memLoad (src+UInt256.ofNat 96) mem) 192 (by decide)).symm.trans hv

theorem AttestationMemoryView.uidTimeBounds {mem : ByteArray} {src dataPtr : UInt256} {a : AttestationRecord}
    (h : AttestationMemoryView mem src dataPtr a) : a.time.toNat < 2^64 ∧ a.expirationTime.toNat < 2^64 := by
  have hf := h.fields
  simp only [attestationEncodeHeadWords,attestationEncodeFirstWords,attestationEncodeLastWords,
    AttestationRecord.words,List.cons_append,List.nil_append,List.cons.injEq,and_true] at hf
  obtain ⟨_,_,ht,he,_⟩ := hf
  rw [← ht,← he]
  exact ⟨u256LandMaskToNatLtOfToNat _ _ (by decide),u256LandMaskToNatLtOfToNat _ _ (by decide)⟩

end Benchmarks.EAS.EAS
