import Benchmarks.EAS.EAS.RecordTailRun
import Benchmarks.EAS.EAS.ArrayFrameViews
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem recordResultPtr_preserve {before after : ByteArray} {limit : Nat} (site : UIDSite)
    (hp : MemoryPrefix before after limit) (hlo : 160 ≤ limit) (hin : 160 ≤ before.size) :
    recordResultPtr site after = recordResultPtr site before := by
  cases site with
  | single _ _ _ _ _ _ _ _ => rfl
  | many _ _ _ _ _ _ => exact memLoad_of_prefix hp _ (by decide) hlo hin

theorem RecordTailMemoryView.preserveValues {before after valueMemory : ByteArray} {site : UIDSite}
    {t3 t4 uidPtr value : UInt256} {ptrs values uids : List UInt256} {heap next : Nat}
    (h : RecordTailMemoryView before site t3 t4 uidPtr ptrs values uids value heap valueMemory)
    (hp : MemoryPrefix before after heap) (hvp : MemoryPrefix valueMemory after heap) (hb : heap < UInt256.size)
    (hlo : 160 ≤ heap) (hin : 160 ≤ before.size) (hn : heap ≤ next)
    (hh : memLoad (UInt256.ofNat 64) after = UInt256.ofNat next) :
    RecordTailMemoryView after site t3 t4 uidPtr ptrs values uids value next := by
  have hu := h.uidArray.span
  have hc := h.requestCovered
  have hr := h.requestEnd
  have hnload : (refUIDPtr site t3+UInt256.ofNat 160).toNat = (refUIDPtr site t3).toNat+160 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have hresult := recordResultPtr_preserve site hp hlo hin
  refine ⟨(h.records.preserve hp hb).mono hn,(h.valueArray.preserve hvp hb).mono hn,
    (h.uidArray.preserve hp hb).mono hn,h.lengthValues,h.lengthUIDs,h.uidRecords,h.recordValues,
    h.requestLow,h.requestEnd,le_trans h.requestCovered hp.size,?_,?_,?_,?_,?_,hh⟩
  · exact (memLoad_of_prefix hp _ (by rw [hnload]; have := h.requestLow; omega)
      (by rw [hnload]; omega) (by rw [hnload]; omega)).trans h.requestValue
  · exact (recordUIDsPtr_preserve site hp hlo hin h.resultLow (by have := h.resultEnd; omega) h.resultCovered hb).trans h.uidPointer
  · rw [hresult]; exact h.resultLow
  · rw [hresult]; exact h.resultEnd
  · rw [hresult]; exact le_trans h.resultCovered hp.size

theorem RecordTailMemoryView.preserve {before after : ByteArray} {site : UIDSite}
    {t3 t4 uidPtr value : UInt256} {ptrs values uids : List UInt256} {heap next : Nat}
    (h : RecordTailMemoryView before site t3 t4 uidPtr ptrs values uids value heap)
    (hp : MemoryPrefix before after heap) (hb : heap < UInt256.size)
    (hlo : 160 ≤ heap) (hin : 160 ≤ before.size) (hn : heap ≤ next)
    (hh : memLoad (UInt256.ofNat 64) after = UInt256.ofNat next) :
    RecordTailMemoryView after site t3 t4 uidPtr ptrs values uids value next :=
  h.preserveValues hp hp hb hlo hin hn hh

theorem recordTailMemory_prefix {mem : ByteArray} (site : UIDSite) {src t3 t4 value uidPtr word : UInt256}
    {ptrs values uids : List UInt256} {heap i : Nat}
    (h : RecordTailMemoryView mem site t3 t4 uidPtr ptrs values uids value heap)
    (hi : i < ptrs.length) (hb : heap < UInt256.size) :
    MemoryPrefix mem (recordTailMemory mem site src t3 t4 value uidPtr word i) uidPtr.toNat := by
  have hu := h.uidArray.span
  have ha := h.uidRecords
  have hv := h.recordValues
  have hn : i < uids.length := by rw [h.lengthUIDs]; exact hi
  rw [recordTailMemory_eq site src t3 t4 value uidPtr word i heap
    (by have := h.records.low; have := h.records.covered; omega) h.records.low h.valueArray.low h.uidArray.low hb
    (by omega) h.heapRead]
  unfold arrayTripleStore
  exact (((memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega))).trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega)))).trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega)))).trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega)))

end Benchmarks.EAS.EAS
