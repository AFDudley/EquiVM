import Benchmarks.EAS.EAS.SchemaMemory
import Benchmarks.EAS.EAS.RecordTailPreserve
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem SchemaMemoryView.write_disjoint {mem : ByteArray} {ptr : UInt256} {s : SchemaRecord}
    (h : SchemaMemoryView mem ptr s) (dst : Nat) (word : UInt256) (hb : ptr.toNat+128 < UInt256.size)
    (hd : ptr.toNat+128 ≤ dst ∨ dst+32 ≤ ptr.toNat) :
    SchemaMemoryView (Reasoning.Theory.writeWord mem dst word) ptr s := by
  have hc := h.covered
  have hload (p : UInt256) (hlo : ptr.toNat ≤ p.toNat) (hhi : p.toNat+32 ≤ ptr.toNat+128) :
      memLoad p (Reasoning.Theory.writeWord mem dst word) = memLoad p mem := by
    rcases hd with hd | hd
    · exact memLoad_write_below _ _ _ _ (by omega) (by omega)
    · exact memLoad_write_above _ _ _ _ (by omega) (by omega)
  refine ⟨h.low,?_,(hload ptr (le_refl _) (by omega)).trans h.uid,?_,?_⟩
  · rw [writeWord_sparse_size]; omega
  · have hn : (ptr+UInt256.ofNat 32).toNat = ptr.toNat+32 := uadd_word_ofNat_toNat _ _ (by omega)
    exact (hload _ (by rw [hn]; omega) (by rw [hn]; omega)).trans h.resolver
  · have hn : (ptr+UInt256.ofNat 64).toNat = ptr.toNat+64 := uadd_word_ofNat_toNat _ _ (by omega)
    exact (hload _ (by rw [hn]; omega) (by rw [hn]; omega)).trans h.revocable

theorem schemaTailMemory_view {mem : ByteArray} (site : UIDSite) {ptr src t3 t4 value uidPtr word : UInt256}
    {s : SchemaRecord} {ptrs values uids : List UInt256} {heap i : Nat}
    (h : RecordTailMemoryView mem site t3 t4 uidPtr ptrs values uids value heap)
    (hs : SchemaMemoryView mem ptr s) (hi : i < ptrs.length) (hb : heap < UInt256.size)
    (hlo : uidPtr.toNat+32+32*uids.length ≤ ptr.toNat)
    (hhi : ptr.toNat+128 ≤ (recordArrayPtr site t3 t4).toNat) :
    SchemaMemoryView (recordTailMemory mem site src t3 t4 value uidPtr word i) ptr s := by
  have ha := h.records.span
  have hv := h.recordValues
  have hiu : i < uids.length := by rw [h.lengthUIDs]; exact hi
  rw [recordTailMemory_eq site src t3 t4 value uidPtr word i heap
    (by have := hs.covered; have := hs.low; omega) h.records.low h.valueArray.low h.uidArray.low hb
    (by omega) h.heapRead]
  unfold arrayTripleStore
  exact (((hs.write_disjoint _ src (by omega) (Or.inl (by omega))).write_disjoint
    _ value (by omega) (Or.inl (by omega))).write_disjoint
    _ word (by omega) (Or.inr (by omega))).write_disjoint _ word (by omega) (Or.inl (by omega))

end Benchmarks.EAS.EAS
