import Benchmarks.EAS.EAS.NewRecordRun
import Benchmarks.EAS.EAS.UIDLoop
import Benchmarks.EAS.EAS.RecordStoreRun
import Benchmarks.EAS.EAS.RefUIDRun
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: transport unaffected local bindings across several source fragments.
def LocalsPreserveExcept (names : List Ident) (before after : Store) : Prop :=
  ∀ name, name ∉ names → after.get? name = before.get? name

theorem LocalsPreserveExcept.trans {names : List Ident} {a b c : Store}
    (h : LocalsPreserveExcept names a b) (h' : LocalsPreserveExcept names b c) : LocalsPreserveExcept names a c := by
  intro name hn
  exact (h' name hn).trans (h name hn)

theorem beq_false_of_mem_not_mem {names : List Ident} {name key : Ident}
    (hn : name ∉ names) (hk : key ∈ names) : (key == name) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  exact hn ((beq_iff_eq.mp h) ▸ hk)

def recordProcessChanged : List Ident := ["__c2$allocation","__c2","$EAS.freeMemory","allocation$allocation","allocation",
  "attestation","uid","bump","__c3$allocation","__c3","__c4$allocation","__c4"]
abbrev RecordProcessKeep := LocalsPreserveExcept recordProcessChanged

theorem newRecordLocals_keep (L : Store) (r : AttestationRequestRecord) (schema time : UInt256)
    (attester : AccountAddress) (heap : Nat) : RecordProcessKeep L (newRecordLocals L r schema time attester heap) := by
  intro name hn
  have hne (key : Ident) (hk : key ∈ recordProcessChanged) : (key == name) = false := beq_false_of_mem_not_mem hn hk
  simp (disch := apply hne; decide) only [newRecordLocals,newAttestationLocals,store_get_ne,
    allocateBlockLocals_get,readTimeLocals,heapResultLocals_get]

theorem UIDLoopKeep.recordProcess {L L' : Store} (h : UIDLoopKeep L L') : RecordProcessKeep L L' := by
  intro name hn
  apply h name <;> exact beq_false_of_mem_not_mem hn (by decide)

theorem recordScalarLocals_keep (L : Store) (a : AttestationRecord) (word : UInt256) :
    RecordProcessKeep L (recordScalarLocals L a word) := by
  intro name hn
  exact recordScalarLocals_get _ _ _ _ (beq_false_of_mem_not_mem hn (by decide))

theorem refUIDLocals_get (L : Store) (uid value : UInt256) (heap : Nat) (name : Ident)
    (h1 : ("__c4$allocation" == name) = false) (h2 : ("__c4" == name) = false) (h3 : ("$EAS.freeMemory" == name) = false) :
    (refUIDLocals L uid value heap).get? name = L.get? name := by
  unfold refUIDLocals
  split
  · rfl
  · simp only [unpackHeapLocals,store_get_ne _ _ h1,store_get_ne _ _ h2,store_get_ne _ _ h3]

theorem refUIDLocals_heap {L : Store} {uid value : UInt256} {heap : Nat}
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    (refUIDLocals L uid value heap).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) := by
  unfold refUIDLocals
  split
  · exact hh
  · exact store_get_self _ _ _

theorem refUIDLocals_keep (L : Store) (uid value : UInt256) (heap : Nat) :
    RecordProcessKeep L (refUIDLocals L uid value heap) := by
  intro name hn
  apply refUIDLocals_get <;> exact beq_false_of_mem_not_mem hn (by decide)

end Benchmarks.EAS.EAS
