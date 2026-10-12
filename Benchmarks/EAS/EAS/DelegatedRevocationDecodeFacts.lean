import Benchmarks.EAS.EAS.DelegatedRevocationDecode
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem decodeDelegatedRevocationFields_facts {cd : ByteArray} {root : UInt256} {r : DelegatedRevocationBatch}
    (h : decodeDelegatedRevocationFields cd root = some r) :
    delegatedBatchArrayAccess cd root 32 ∧ decodeRevocationArray cd (delegatedBatchArray cd root 32) = some r.data ∧
    delegatedBatchArrayAccess cd root 64 ∧ decodeSignatureArray cd (delegatedBatchArray cd root 64) = some r.signatures ∧
    delegatedBatchAddressClean cd root ∧ r.schema = calldataWord cd root.toNat ∧
    r.revoker = AccountAddress.ofNat (calldataWord cd (root+UInt256.ofNat 96).toNat).toNat := by
  unfold decodeDelegatedRevocationFields at h
  split at h
  · cases h
  rename_i ha
  have ha' := not_not.mp ha
  cases hd : decodeRevocationArray cd (delegatedBatchArray cd root 32) with
  | none => simp only [hd,bind,Option.bind_none] at h; cases h
  | some rs =>
    simp only [hd,bind,Option.bind_some] at h
    split at h
    · cases h
    rename_i hs
    have hs' := not_not.mp hs
    cases ht : decodeSignatureArray cd (delegatedBatchArray cd root 64) with
    | none => simp only [ht,Option.bind_none] at h; cases h
    | some ss =>
      simp only [ht,Option.bind_some] at h
      split at h
      · cases h
      rename_i hc
      have hr : r = ⟨calldataWord cd root.toNat,rs,ss,AccountAddress.ofNat (calldataWord cd (root+UInt256.ofNat 96).toNat).toNat⟩ :=
        (Option.some.inj h).symm
      subst r
      exact ⟨ha',rfl,hs',rfl,not_not.mp hc,rfl,rfl⟩

theorem decodeDelegatedRevocationAt_facts {cd : ByteArray} {root : UInt256} {r : DelegatedRevocationBatch}
    (h : decodeDelegatedRevocationAt cd root = some r) :
    delegatedBatchHeadValid cd root ∧ decodeDelegatedRevocationFields cd root = some r := by
  unfold decodeDelegatedRevocationAt at h
  split at h
  · exact ⟨‹_›,h⟩
  · cases h

theorem decodeDelegatedRevocation_facts {cd : ByteArray} {base : UInt256} {i : Nat} {r : DelegatedRevocationBatch}
    (h : decodeDelegatedRevocation cd base i = some r) :
    delegatedBatchReferenceValid cd base i ∧ decodeDelegatedRevocationAt cd (multiRequestRoot cd base i) = some r := by
  unfold decodeDelegatedRevocation at h
  split at h
  · exact ⟨‹_›,h⟩
  · cases h

end Benchmarks.EAS.EAS
