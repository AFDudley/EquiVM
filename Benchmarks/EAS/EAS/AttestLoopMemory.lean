import Benchmarks.EAS.EAS.AttestRequestSite
import Benchmarks.EAS.EAS.AttestRecordRegion
import Benchmarks.EAS.EAS.RequestArrayMemory
import Benchmarks.EAS.EAS.WordArrayReflect
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

structure AttestLoopMemory (mem : ByteArray) (site : UIDSite) (t3 t4 uidPtr : UInt256)
    (rs : List AttestationRequestRecord) (s : SchemaRecord) (attester : AccountAddress)
    (ptrs values uids : List UInt256) (ats : List AttestationRecord) (heap : Nat) : Prop where
  uidLow : 224 ≤ uidPtr.toNat
  requests : AttestationRequestArrayMemoryView mem (attestRequestArrayPtr site mem) rs uidPtr.toNat
  schemaView : SchemaMemoryView mem (requestSchemaPtr site) s
  schemaLow : uidPtr.toNat+32+32*uids.length ≤ (requestSchemaPtr site).toNat
  schemaHigh : (requestSchemaPtr site).toNat+128 ≤ (recordArrayPtr site t3 t4).toNat
  records : WordArrayMemoryView mem (recordArrayPtr site t3 t4) ptrs heap
  valueArray : WordArrayMemoryView (recordPadding mem heap) (recordValuesPtr site t4) values heap
  valueCovered : (recordValuesPtr site t4).toNat+32 ≤ mem.size
  uidArray : WordArrayMemoryView mem uidPtr uids heap
  recordValues : (recordArrayPtr site t3 t4).toNat+32+32*ptrs.length ≤ (recordValuesPtr site t4).toNat
  lengthRequests : ptrs.length = rs.length
  lengthValues : values.length = ptrs.length
  lengthUIDs : uids.length = ptrs.length
  regions : AttestRecordRegions mem uidPtr (recordArrayPtr site t3 t4) (recordValuesPtr site t4) ptrs ats heap
  uidPointer : recordUIDsPtr site mem = uidPtr
  resultLow : 96 ≤ (recordResultPtr site mem).toNat
  resultEnd : (recordResultPtr site mem).toNat+64 ≤ uidPtr.toNat
  resultCovered : (recordResultPtr site mem).toNat+64 ≤ mem.size
  attesterWord : recordCreateAttester site mem = UInt256.ofNat attester.val
  heapRead : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat heap

@[simp] theorem attestLoopMemory_requestSite (mem : ByteArray) (site : UIDSite) (t3 t4 uidPtr ptr : UInt256)
    (rs : List AttestationRequestRecord) (s : SchemaRecord) (attester : AccountAddress)
    (ptrs values uids : List UInt256) (ats : List AttestationRecord) (heap : Nat) :
    AttestLoopMemory mem (attestRequestSite site ptr) (attestRequestT3 site t3 ptr) t4 uidPtr rs s attester ptrs values uids ats heap ↔
      AttestLoopMemory mem site t3 t4 uidPtr rs s attester ptrs values uids ats heap := by
  cases site <;> constructor <;> intro h <;>
    exact ⟨h.uidLow,h.requests,h.schemaView,h.schemaLow,h.schemaHigh,h.records,h.valueArray,h.valueCovered,h.uidArray,
      h.recordValues,h.lengthRequests,h.lengthValues,h.lengthUIDs,h.regions,h.uidPointer,
      h.resultLow,h.resultEnd,h.resultCovered,h.attesterWord,h.heapRead⟩

theorem AttestLoopMemory.tailView {mem : ByteArray} {site : UIDSite} {t3 t4 uidPtr ptr dp : UInt256}
    {rs : List AttestationRequestRecord} {r : AttestationRequestRecord} {s : SchemaRecord} {attester : AccountAddress}
    {ptrs values uids : List UInt256} {ats : List AttestationRecord} {heap : Nat}
    (h : AttestLoopMemory mem site t3 t4 uidPtr rs s attester ptrs values uids ats heap)
    (hv : AttestationRequestMemoryView mem ptr dp r) (he : ptr.toNat+192 ≤ uidPtr.toNat) :
    RecordTailMemoryView mem (attestRequestSite site ptr) (attestRequestT3 site t3 ptr) t4 uidPtr ptrs values uids r.value heap (recordPadding mem heap) := by
  have hsl := h.schemaLow
  have hsh := h.schemaHigh
  refine ⟨?_,?_,h.uidArray,h.lengthValues,h.lengthUIDs,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,h.heapRead⟩
  · simpa only [attestRequestSite_recordArray] using h.records
  · simpa only [attestRequestSite_values] using h.valueArray
  · simp only [attestRequestSite_recordArray]; omega
  · simpa only [attestRequestSite_recordArray,attestRequestSite_values] using h.recordValues
  · simpa only [attestRequestSite_ref] using hv.low
  · simpa only [attestRequestSite_ref] using he
  · simpa only [attestRequestSite_ref] using hv.covered
  · simpa only [attestRequestSite_ref] using hv.value
  · simpa only [attestRequestSite_uids] using h.uidPointer
  · simpa only [attestRequestSite_result] using h.resultLow
  · simpa only [attestRequestSite_result] using h.resultEnd
  · simpa only [attestRequestSite_result] using h.resultCovered

theorem attestRequestArrayPtr_preserve {before after : ByteArray} {limit : Nat} (site : UIDSite)
    (hp : MemoryPrefix before after limit) (hlo : 224 ≤ limit) (hin : 224 ≤ before.size) :
    attestRequestArrayPtr site after = attestRequestArrayPtr site before := by
  cases site with
  | single _ _ _ _ _ _ _ _ => rfl
  | many _ _ _ _ _ _ => exact memLoad_of_prefix hp _ (by decide) hlo hin

theorem recordCreateAttester_preserve {before after : ByteArray} {limit : Nat} (site : UIDSite)
    (hp : MemoryPrefix before after limit) (hlo : 192 ≤ limit) (hin : 192 ≤ before.size) :
    recordCreateAttester site after = recordCreateAttester site before := by
  cases site with
  | single _ _ _ _ _ _ _ _ => rfl
  | many _ _ _ _ _ _ =>
    unfold recordCreateAttester
    rw [memLoad_of_prefix hp (UInt256.ofNat 160) (by decide) hlo hin]

end Benchmarks.EAS.EAS
