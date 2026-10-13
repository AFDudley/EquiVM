import Benchmarks.EAS.EAS.RecordTailPreserve
import Benchmarks.EAS.EAS.RecordDisjoint
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem recordTailMemory_record {mem : ByteArray} (site : UIDSite)
    {src dataPtr t3 t4 value uidPtr word : UInt256} {a : AttestationRecord}
    {ptrs values uids : List UInt256} {heap i : Nat}
    (h : RecordTailMemoryView mem site t3 t4 uidPtr ptrs values uids value heap)
    (ha : AttestationMemoryView mem src dataPtr a) (hi : i < ptrs.length) (hb : heap < UInt256.size)
    (hs : src.toNat+320 ≤ heap) (hvalues : (recordValuesPtr site t4).toNat+32+32*values.length ≤ src.toNat)
    (hd : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ uidPtr.toNat) :
    AttestationMemoryView (recordTailMemory mem site src t3 t4 value uidPtr word i) src dataPtr a := by
  have hu := h.uidArray.span
  have hru := h.uidRecords
  have hrv := h.recordValues
  have hiv : i < values.length := by rw [h.lengthValues]; exact hi
  have hiu : i < uids.length := by rw [h.lengthUIDs]; exact hi
  rw [recordTailMemory_eq site src t3 t4 value uidPtr word i heap
    (by have := ha.sourceCovered; have := ha.sourceLow; omega) h.records.low h.valueArray.low h.uidArray.low hb
    (by omega) h.heapRead]
  unfold arrayTripleStore
  exact (((ha.write_disjoint _ src (by omega) (Or.inr (by omega)) (Or.inl (by omega))).write_disjoint
    _ value (by omega) (Or.inr (by omega)) (Or.inl (by omega))).write_disjoint
    _ word (by omega) (Or.inr (by omega)) (Or.inl (by omega))).write_disjoint
    _ word (by omega) (Or.inl hs) (Or.inl (by omega))

end Benchmarks.EAS.EAS
