import Benchmarks.EAS.EAS.RevokeStoreCopyRun
import Benchmarks.EAS.EAS.RevokeUpdateSource
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

structure RevokeLoopLocals (L : Store) (site : RevokeSite) (rs : List RevocationRequestRecord)
    (s : SchemaRecord) (ats : List AttestationRecord) (values : List UInt256) (i heap : Nat) : Prop where
  data : L.get? "data" = some (.array (rs.map RevocationRequestRecord.tuple))
  length : L.get? "length" = some (.int (Int.ofNat rs.length))
  schema : L.get? "schema" = some (wordBytes32Value site.schema)
  schemaRecord : L.get? "schemaRecord" = some s.value
  revoker : L.get? "revoker" = some (.address site.revoker)
  available : L.get? "availableValue" = some (.int (Int.ofNat site.available.toNat))
  last : L.get? "last" = some (.bool site.last)
  attestations : L.get? "attestations" = some (.array (ats.map AttestationRecord.value))
  values : L.get? "values" = some (.array (values.map (fun w => Value.int (Int.ofNat w.toNat))))
  index : L.get? "i" = some (.int (Int.ofNat i))
  heap : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))
  db : L.get? "_db" = none

def revokeReadLocals (L : Store) (r : RevocationRequestRecord) (heap : Nat) : Store :=
  revokeAliasLocals (revokeRequestLocals L r heap) r.uid

theorem revokeReadLocals_get (L : Store) (r : RevocationRequestRecord) (heap : Nat) (name : Ident)
    (hn : name ∉ ["request$allocation","request","attestation","$EAS.freeMemory"]) :
    (revokeReadLocals L r heap).get? name = L.get? name := by
  have hne (key : Ident) (hk : key ∈ ["request$allocation","request","attestation","$EAS.freeMemory"]) :
      (key == name) = false := beq_false_of_mem_not_mem hn hk
  simp (disch := apply hne; decide) only [revokeReadLocals,revokeAliasLocals,revokeRequestLocals,heapResultLocals_get,store_get_ne]

theorem revokeReadLocals_alias (L : Store) (r : RevocationRequestRecord) (heap : Nat) :
    (revokeReadLocals L r heap).get? "attestation" = some (.storageRef (attestationER r.uid) attestationType) := store_get_self _ _ _
theorem revokeReadLocals_request (L : Store) (r : RevocationRequestRecord) (heap : Nat) :
    (revokeReadLocals L r heap).get? "request" = some r.struct := by
  unfold revokeReadLocals revokeAliasLocals revokeRequestLocals
  rw [store_get_ne _ _ (by decide)]
  exact heapResultLocals_result _ _ _ _ _ _ (by decide)
theorem revokeReadLocals_heap (L : Store) (r : RevocationRequestRecord) (heap : Nat) :
    (revokeReadLocals L r heap).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) := by
  unfold revokeReadLocals revokeAliasLocals revokeRequestLocals
  rw [store_get_ne _ _ (by decide)]
  exact heapResultLocals_heap _ _ _ _ _ _

theorem revokeStoreCopyLocals_get (L : Store) (time : UInt256) (old heap : Nat) (a : AttestationRecord) (name : Ident)
    (hn : name ∉ ["__c1$allocation","__c1","copied$allocation","copied","$EAS.freeMemory"]) :
    (revokeStoreCopyLocals L time old heap a).get? name = L.get? name := by
  have hne (key : Ident) (hk : key ∈ ["__c1$allocation","__c1","copied$allocation","copied","$EAS.freeMemory"]) :
      (key == name) = false := beq_false_of_mem_not_mem hn hk
  simp (disch := apply hne; decide) only [revokeStoreCopyLocals,readTimeLocals,heapResultLocals_get]

def revokeIterationLocals (L : Store) (r : RevocationRequestRecord) (time : UInt256) (old heap : Nat)
    (ats : List AttestationRecord) (values : List UInt256) (a : AttestationRecord) (i : Nat) : Store :=
  revokeUpdateLocals (revokeStoreCopyLocals (revokeReadLocals L r old) time old heap a) ats values a r.value i

theorem RevokeLoopLocals.next {L : Store} {site : RevokeSite} {rs : List RevocationRequestRecord} {s : SchemaRecord}
    {ats : List AttestationRecord} {values : List UInt256} {i old heap : Nat} {r : RevocationRequestRecord}
    {time : UInt256} {a : AttestationRecord}
    (h : RevokeLoopLocals L site rs s ats values i old) :
    RevokeLoopLocals (revokeIterationLocals L r time old heap ats values a i)
      site rs s (ats.set i a) (values.set i r.value) (i+1) heap := by
  have keep (name : Ident)
      (hn : name ∉ ["request$allocation","request","attestation","__c1$allocation","__c1",
        "copied$allocation","copied","$EAS.freeMemory","attestations","values","i"]) :
      (revokeIterationLocals L r time old heap ats values a i).get? name = L.get? name := by
    have hne (key : Ident) (hk : key ∈ ["request$allocation","request","attestation","__c1$allocation","__c1",
        "copied$allocation","copied","$EAS.freeMemory","attestations","values","i"]) :
        (key == name) = false := beq_false_of_mem_not_mem hn hk
    simp (disch := apply hne; decide) only [revokeIterationLocals,revokeUpdateLocals,revokeStoreCopyLocals,
      readTimeLocals,revokeReadLocals,revokeAliasLocals,revokeRequestLocals,heapResultLocals_get,store_get_ne]
  refine ⟨(keep "data" (by decide)).trans h.data,(keep "length" (by decide)).trans h.length,
    (keep "schema" (by decide)).trans h.schema,(keep "schemaRecord" (by decide)).trans h.schemaRecord,
    (keep "revoker" (by decide)).trans h.revoker,(keep "availableValue" (by decide)).trans h.available,
    (keep "last" (by decide)).trans h.last,?_,?_,?_,?_,(keep "_db" (by decide)).trans h.db⟩
  · simp (disch := decide) only [revokeIterationLocals,revokeUpdateLocals,store_get_ne,store_get_self]
  · simp (disch := decide) only [revokeIterationLocals,revokeUpdateLocals,store_get_ne,store_get_self]
  · exact store_get_self _ _ _
  · simp (disch := decide) only [revokeIterationLocals,revokeUpdateLocals,revokeStoreCopyLocals,store_get_ne,heapResultLocals_heap]

end Benchmarks.EAS.EAS
