import Benchmarks.EAS.EAS.AttestLoopMemory
import Benchmarks.EAS.EAS.AttestRecordRegionsTail
import Benchmarks.EAS.EAS.SchemaTailMemory
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem AttestLoopMemory.next {before mid : ByteArray} {site : UIDSite} {src dp t3 t4 uidPtr value word : UInt256}
    {rs : List AttestationRequestRecord} {s : SchemaRecord} {attester : AccountAddress}
    {ptrs values uids : List UInt256} {ats : List AttestationRecord} {a : AttestationRecord} {next i : Nat}
    (h : AttestLoopMemory before site t3 t4 uidPtr rs s attester ptrs values uids ats src.toNat)
    (hcore : MemoryPrefix before mid src.toNat)
    (hfoot : MemoryPrefix before (recordTailMemory mid site src t3 t4 value uidPtr word i) uidPtr.toNat)
    (hm : RecordTailMemoryView mid site t3 t4 uidPtr ptrs values uids value next)
    (hv : AttestationMemoryView mid src dp a) (hi : i < ptrs.length) (hb : next < UInt256.size)
    (hn : src.toNat+320 ≤ next) (hd : dp.toNat+32+32*((a.data.size+31)/32) ≤ uidPtr.toNat)
    (hu' : WordArrayMemoryView (recordTailMemory mid site src t3 t4 value uidPtr word i) uidPtr (uids.set i word) next)
    (ha' : WordArrayMemoryView (recordTailMemory mid site src t3 t4 value uidPtr word i) (recordArrayPtr site t3 t4) (ptrs.set i src) next)
    (hv' : WordArrayMemoryView (recordTailMemory mid site src t3 t4 value uidPtr word i) (recordValuesPtr site t4) (values.set i value) next)
    (hh' : memLoad (UInt256.ofNat 64) (recordTailMemory mid site src t3 t4 value uidPtr word i) = UInt256.ofNat next) :
    AttestLoopMemory (recordTailMemory mid site src t3 t4 value uidPtr word i) site t3 t4 uidPtr rs s attester
      (ptrs.set i src) (values.set i value) (uids.set i word) (ats.set i a) next := by
  have hul := h.uidLow
  have hus := h.uidArray.span
  have huc := h.uidArray.covered
  have has := h.records.span
  have hsh := h.schemaHigh
  have hsize : 224 ≤ before.size := by omega
  have huheap : uidPtr.toNat ≤ src.toNat := by omega
  have hrptr := attestRequestArrayPtr_preserve site hfoot hul hsize
  have hresult := recordResultPtr_preserve site hfoot (by omega) (by omega)
  have hschema := h.schemaView.preserve hcore (by omega) src.val.isLt
  have hregions := h.regions.preserve (next := next) hcore src.val.isLt huheap (by omega)
  refine ⟨hul,?_,schemaTailMemory_view site hm hschema hi hb h.schemaLow h.schemaHigh,?_,h.schemaHigh,
    ha',hv'.preserve (recordPadding_prefix _ _) hb,(by have := hv'.covered; omega),hu',?_,?_,?_,?_,hregions.tail site hm hv hi hb hn h.valueArray.span hd,?_,?_,?_,?_,?_,hh'⟩
  · rw [hrptr]
    exact h.requests.preserve hfoot uidPtr.val.isLt
  · simpa only [List.length_set] using h.schemaLow
  · simpa only [List.length_set] using h.recordValues
  · simpa only [List.length_set] using h.lengthRequests
  · simpa only [List.length_set] using h.lengthValues
  · simpa only [List.length_set] using h.lengthUIDs
  · exact (recordUIDsPtr_preserve site hfoot (by omega) (by omega) h.resultLow h.resultEnd h.resultCovered uidPtr.val.isLt).trans h.uidPointer
  · rw [hresult]; exact h.resultLow
  · rw [hresult]; exact h.resultEnd
  · rw [hresult]; exact le_trans h.resultCovered hfoot.size
  · exact (recordCreateAttester_preserve site hfoot (by omega) (by omega)).trans h.attesterWord

end Benchmarks.EAS.EAS
