import Benchmarks.EAS.EAS.AttestReadGuards
import Benchmarks.EAS.EAS.RecordTailSource
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

structure AttestLoopLocals (L : Store) (rs : List AttestationRequestRecord) (s : SchemaRecord)
    (schema : UInt256) (attester : AccountAddress) (available : UInt256) (last : Bool)
    (ats : List AttestationRecord) (values uids : List UInt256) (used : UInt256) (i heap : Nat) : Prop where
  data : L.get? "data" = some (.array (rs.map AttestationRequestRecord.tuple))
  length : L.get? "length" = some (.int (Int.ofNat rs.length))
  schema : L.get? "schema" = some (wordBytes32Value schema)
  schemaRecord : L.get? "schemaRecord" = some s.value
  attester : L.get? "attester" = some (.address attester)
  available : L.get? "availableValue" = some (.int (Int.ofNat available.toNat))
  last : L.get? "last" = some (.bool last)
  attestations : L.get? "attestations" = some (.array (ats.map AttestationRecord.value))
  values : L.get? "values" = some (.array (values.map (fun w => Value.int (Int.ofNat w.toNat))))
  result : L.get? "res" = some (attestationsResultValue uids used)
  index : L.get? "i" = some (.int (Int.ofNat i))
  heap : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))
  db : L.get? "_db" = none

theorem recordTailLocals_get (L : Store) (ats : List AttestationRecord) (values uids : List UInt256)
    (used : UInt256) (a : AttestationRecord) (value uid : UInt256) (i : Nat) (name : Ident)
    (h1 : ("i" == name) = false) (h2 : ("res" == name) = false)
    (h3 : ("values" == name) = false) (h4 : ("attestations" == name) = false) :
    (recordTailLocals L ats values uids used a value uid i).get? name = L.get? name := by
  simp only [recordTailLocals,recordArraysLocals,store_get_ne _ _ h1,store_get_ne _ _ h2,store_get_ne _ _ h3,store_get_ne _ _ h4]

theorem AttestLoopLocals.afterRecord {L Lp : Store} {rs : List AttestationRequestRecord} {s : SchemaRecord}
    {schema time available used uid : UInt256} {attester : AccountAddress} {last : Bool}
    {ats : List AttestationRecord} {values uids : List UInt256} {r : AttestationRequestRecord}
    {a : AttestationRecord} {i heap next : Nat}
    (h : AttestLoopLocals L rs s schema attester available last ats values uids used i heap)
    (hk : RecordProcessKeep (attestReadGuardsLocals L r time heap) Lp)
    (hh : Lp.get? "$EAS.freeMemory" = some (.int (Int.ofNat next))) :
    AttestLoopLocals (recordTailLocals Lp ats values uids used a r.value uid i) rs s schema attester available last
      (ats.set i a) (values.set i r.value) (uids.set i uid) used (i+1) next := by
  have keep (name : Ident)
      (hf : name ∉ ["request$allocation","request","__c1$allocation","__c1","$EAS.freeMemory"])
      (hp : name ∉ recordProcessChanged)
      (h1 : ("i" == name) = false) (h2 : ("res" == name) = false)
      (h3 : ("values" == name) = false) (h4 : ("attestations" == name) = false) :
      (recordTailLocals Lp ats values uids used a r.value uid i).get? name = L.get? name :=
    (recordTailLocals_get _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4).trans
      ((hk name hp).trans (attestReadGuardsLocals_get _ _ _ _ _ hf))
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (keep "data" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.data
  · exact (keep "length" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.length
  · exact (keep "schema" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.schema
  · exact (keep "schemaRecord" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.schemaRecord
  · exact (keep "attester" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.attester
  · exact (keep "availableValue" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.available
  · exact (keep "last" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.last
  · simp (disch := decide) only [recordTailLocals,recordArraysLocals,store_get_ne,store_get_self]
  · simp (disch := decide) only [recordTailLocals,recordArraysLocals,store_get_ne,store_get_self]
  · simp (disch := decide) only [recordTailLocals,recordArraysLocals,store_get_ne,store_get_self]
  · exact store_get_self _ _ _
  · exact (recordTailLocals_get _ _ _ _ _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)).trans hh
  · exact (keep "_db" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.db

end Benchmarks.EAS.EAS
