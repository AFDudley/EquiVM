import Benchmarks.EAS.EAS.CheckAttestationCopySource
import Benchmarks.EAS.EAS.DelegatedAttestationVerified
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem checkAttestationCopyData_eq {cd : ByteArray} {base : UInt256} {i : Nat}
    (he : base=checkAttestationCopyBase cd) (hb : base.toNat+32*i<UInt256.size) :
    checkAttestationCopyData cd i=delegatedAttestationDataOffset cd (multiRequestRoot cd base i) := by
  unfold checkAttestationCopyData checkAttestationCopyRoot
  rw [← he,ulit_toNat' _ hb]
  rfl

theorem checkAttestationCopyValid_iff {cd : ByteArray} {base : UInt256} {i len : Nat}
    (he : base=checkAttestationCopyBase cd) (hb : base.toNat+32*i<UInt256.size)
    (hspan : (delegatedAttestationDataOffset cd (multiRequestRoot cd base i)).toNat+32*len<UInt256.size)
    (hsize : cd.size<UInt256.size) :
    checkAttestationCopyValid cd i len ↔
      (delegatedAttestationDataOffset cd (multiRequestRoot cd base i)).toNat+32*len≤cd.size ∧
      ∀ t, t<len → (calldataWord cd ((delegatedAttestationDataOffset cd (multiRequestRoot cd base i)).toNat+32*t)).toNat≤2^64-1 := by
  rw [checkAttestationCopyValid,checkAttestationCopyData_eq he hb,ulit_toNat' _ hspan,ulit_toNat' _ hsize]
  constructor
  · rintro ⟨he,hcaps⟩
    refine ⟨he,fun t ht => ?_⟩
    have h := hcaps t ht
    rw [ulit_toNat' _ (by omega)] at h
    exact h
  · rintro ⟨he,hcaps⟩
    refine ⟨he,fun t ht => ?_⟩
    rw [ulit_toNat' _ (by omega)]
    exact hcaps t ht

theorem delegatedAttestationRecords_view {cd : ByteArray} {root : UInt256}
    (hgood : ∀ t, t<(delegatedAttestationDataLength cd root).toNat →
      delegatedAttestationDataValid cd (delegatedAttestationDataOffset cd root) t)
    (he : (delegatedAttestationDataOffset cd root).toNat+32*(delegatedAttestationDataLength cd root).toNat≤cd.size)
    (hc : ∀ t, t<(delegatedAttestationDataLength cd root).toNat →
      (calldataWord cd ((delegatedAttestationDataOffset cd root).toNat+32*t)).toNat≤2^64-1) :
    RequestArrayCalldataView cd (delegatedAttestationDataOffset cd root) (delegatedAttestationRecords cd root) := by
  constructor
  · simpa only [delegatedAttestationRecords_length] using he
  · intro t ht
    have hn : t<(delegatedAttestationDataLength cd root).toNat := by simpa only [delegatedAttestationRecords_length] using ht
    exact ⟨hc t hn,(hgood t hn).2,(delegatedAttestationRecords_get cd root t ht).symm⟩

end Benchmarks.EAS.EAS
