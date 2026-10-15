import Benchmarks.EAS.EAS.RevokeUpdateEVM
import Benchmarks.EAS.EAS.RevokeRecordRegion
import Benchmarks.EAS.EAS.ArrayDisjoint
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem revokeUpdateMemory_prefix (mem : ByteArray) (site : RevokeSite) (src heap value word : UInt256) (i : Nat)
    (hv : site.records.toNat ≤ site.values.toNat) (hh : site.records.toNat ≤ heap.toNat) :
    MemoryPrefix mem (revokeUpdateMemory mem site src heap value word i) site.records.toNat :=
  ((memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega))).trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega)))).trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl hh))

theorem revokeUpdateMemory_views {mem : ByteArray} (site : RevokeSite) {src value word : UInt256}
    {ptrs values : List UInt256} {heap i : Nat}
    (ha : WordArrayMemoryView mem site.records ptrs heap) (hv : WordArrayMemoryView mem site.values values heap)
    (hav : site.records.toNat+32+32*ptrs.length ≤ site.values.toNat)
    (hia : i < ptrs.length) (hiv : i < values.length) (hb : heap < UInt256.size) :
    WordArrayMemoryView (revokeUpdateMemory mem site src (UInt256.ofNat heap) value word i)
      site.records (ptrs.set i src) heap ∧
    WordArrayMemoryView (revokeUpdateMemory mem site src (UInt256.ofNat heap) value word i)
      site.values (values.set i value) heap ∧
    memLoad (UInt256.ofNat 64) (revokeUpdateMemory mem site src (UInt256.ofNat heap) value word i) =
      memLoad (UInt256.ofNat 64) mem := by
  have ha1 := ha.set i hia src hb
  have hv1 := hv.write_disjoint (site.records.toNat+32+32*i) src hb (Or.inr (by omega))
  have ha2 := ha1.write_disjoint (site.values.toNat+32+32*i) value hb (Or.inl (by simp only [List.length_set]; omega))
  have hv2 := hv1.set i hiv value hb
  have hn := ulit_toNat' heap hb
  refine ⟨?_,?_,?_⟩
  · simpa only [revokeUpdateMemory,revokeValuesLogMemory,hn] using ha2.write_disjoint heap word hb (Or.inl ha2.span)
  · simpa only [revokeUpdateMemory,revokeValuesLogMemory,hn] using hv2.write_disjoint heap word hb (Or.inl hv2.span)
  · have hsize : 96 ≤ mem.size := by have := ha.low; have := ha.covered; omega
    have hlo : 96 ≤ heap := by have := ha.low; have := ha.span; omega
    simp only [revokeUpdateMemory,revokeValuesLogMemory,hn]
    rw [memLoad_write_below _ heap (UInt256.ofNat 64) word hlo (by change 96 ≤ _; simp only [writeWord_sparse_size]; omega),
      memLoad_write_below _ _ (UInt256.ofNat 64) value (by have := hv.low; change 64+32 ≤ _; omega)
        (by change 96 ≤ _; rw [writeWord_sparse_size]; omega),
      memLoad_write_below _ _ (UInt256.ofNat 64) src (by have := ha.low; change 64+32 ≤ _; omega) hsize]

theorem RevokeRecordRegions.update {mem : ByteArray} (site : RevokeSite) {src dp value word : UInt256}
    {ptrs : List UInt256} {ats : List AttestationRecord} {a : AttestationRecord} {heap i : Nat}
    (h : RevokeRecordRegions mem site.records site.values ptrs ats heap)
    (hv : AttestationMemoryView mem src dp a) (hi : i < ptrs.length) (hb : heap < UInt256.size)
    (hav : site.records.toNat+32+32*ptrs.length ≤ site.values.toNat)
    (hs : src.toNat+320 ≤ heap) (hvalues : site.values.toNat+32+32*ptrs.length ≤ src.toNat)
    (hd : dp.toNat+32+32*((a.data.size+31)/32) ≤ heap) (hdlo : src.toNat ≤ dp.toNat) :
    RevokeRecordRegions (revokeUpdateMemory mem site src (UInt256.ofNat heap) value word i)
      site.records site.values (ptrs.set i src) (ats.set i a) heap := by
  have ht : site.records.toNat ≤ site.records.toNat+32+32*ptrs.length ∧
      site.records.toNat+32+32*ptrs.length ≤ site.values.toNat ∧ site.values.toNat ≤ site.values.toNat+32+32*ptrs.length := by omega
  have hn := ulit_toNat' heap hb
  have keep (p : UInt256) (b : AttestationRecord)
      (hp : RevokeRecordRegion mem p b site.records.toNat (site.records.toNat+32+32*ptrs.length)
        site.values.toNat (site.values.toNat+32+32*ptrs.length) heap) :
      RevokeRecordRegion (revokeUpdateMemory mem site src (UInt256.ofNat heap) value word i) p b
        site.records.toNat (site.records.toNat+32+32*ptrs.length) site.values.toNat
        (site.values.toNat+32+32*ptrs.length) heap := by
    simp only [revokeUpdateMemory,revokeValuesLogMemory,hn]
    exact ((hp.write _ src hb (Or.inl ⟨by omega,by omega⟩) ht).write _ value hb
      (Or.inr (Or.inl ⟨by omega,by omega⟩)) ht).write _ word hb (Or.inr (Or.inr (le_refl _))) ht
  have hnew : RevokeRecordRegion mem src a site.records.toNat (site.records.toNat+32+32*ptrs.length)
      site.values.toNat (site.values.toNat+32+32*ptrs.length) heap :=
    ⟨hs,by omega,Or.inr hvalues,dp,hv,hd,Or.inr (by omega)⟩
  simpa only [RevokeRecordRegions,List.length_set] using listForall₂_set (h.imp keep) i (keep src a hnew)

end Benchmarks.EAS.EAS
