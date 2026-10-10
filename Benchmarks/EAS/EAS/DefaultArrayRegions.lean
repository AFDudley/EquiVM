import Benchmarks.EAS.EAS.DefaultArrayRecords
import Benchmarks.EAS.EAS.DefaultArrayTable
import Benchmarks.EAS.EAS.AttestRecordRegion
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem defaultArrayMemory_regions (mem : ByteArray) (heap uid values : UInt256) (len : Nat)
    (hu : 128 ≤ uid.toNat) (hh : heap.toNat ≤ 2^64-1) (hl : len ≤ 2^64-1)
    (huh : uid.toNat ≤ heap.toNat) (hv : allocateNext heap.toNat (32+352*len) ≤ values.toNat)
    (hin : 128 ≤ mem.size) (hz : memLoad (UInt256.ofNat 96) mem = ⟨0⟩) :
    AttestRecordRegions (defaultArrayMemory mem heap len) uid heap values
      (defaultArrayPointers heap len) (List.replicate len defaultAttestationRecord)
      (allocateNext heap.toNat (32+352*len)) := by
  have hn := allocateNext_recordArray hh hl
  let header := arrayAllocationHeaderMemory mem heap len
  have hp : MemoryPrefix mem header heap.toNat :=
    (memoryPrefix_sparse_writeWord _ 64 _ _ (Or.inr (by decide))).trans
      (memoryPrefix_sparse_writeWord _ heap.toNat _ _ (Or.inl (le_refl _)))
  have hz' : memLoad (UInt256.ofNat 96) header = ⟨0⟩ :=
    (memLoad_of_prefix hp (UInt256.ofNat 96) (by decide) (by change 128 ≤ heap.toNat; omega) hin).trans hz
  have hb : heap.toNat+32+352*len < UInt256.size := by change heap.toNat+32+352*len < 2^256; omega
  unfold AttestRecordRegions
  apply List.forall₂_iff_get.mpr
  refine ⟨by simp only [defaultArrayPointers_length,List.length_replicate],?_⟩
  intro i hi hj
  have hi' : i < len := by simpa only [defaultArrayPointers_length] using hi
  have hs : (defaultArrayPointers heap len)[i] = UInt256.ofNat (heap.toNat+32+32*len+320*i) := by
    simp only [defaultArrayPointers,List.getElem_map,List.getElem_range]
  have hsrc : ((defaultArrayPointers heap len)[i]).toNat = heap.toNat+32+32*len+320*i := by
    rw [hs,ulit_toNat' _ (by omega)]
  have ha : (List.replicate len defaultAttestationRecord)[i] = defaultAttestationRecord := List.getElem_replicate _
  simp only [List.get_eq_getElem]
  rw [ha]
  refine ⟨?_,?_,Or.inl ?_,UInt256.ofNat 96,?_,hu⟩
  · rw [hsrc,hn]; omega
  · rw [hsrc,defaultArrayPointers_length]; omega
  · rw [hsrc]; rw [hn] at hv; omega
  · rw [hs]
    exact defaultAttestationSlotsMemory_view header (heap.toNat+32+32*len) (heap.toNat+32) len i
      (by omega) (le_refl _) (by omega) (le_trans hin hp.size) hz' hi'

end Benchmarks.EAS.EAS
