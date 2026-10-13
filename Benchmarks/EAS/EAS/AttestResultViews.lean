import Benchmarks.EAS.EAS.AttestResultAllocate
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem defaultResultMemory_covers (mem : ByteArray) (heap : UInt256) :
    heap.toNat+64 ≤ (defaultResultMemory mem heap).size :=
  writeWordSequence_covers _ _ [⟨0⟩,⟨96⟩] (by decide)

theorem defaultResultMemory_used (mem : ByteArray) (heap : UInt256) :
    memLoad heap (defaultResultMemory mem heap) = ⟨0⟩ := by
  have h := writeWordSequence_load_index (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat 64)))
    heap.toNat [⟨0⟩,⟨96⟩] 0 (by decide) (by simpa only [Nat.mul_zero,Nat.add_zero] using heap.val.isLt)
  simpa only [defaultResultMemory,Nat.mul_zero,Nat.add_zero,u256_ofNat_toNat,List.getElem_cons_zero] using h

theorem attestResultsMemory_view (mem : ByteArray) (heap : UInt256)
    (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1) (hn : allocateNext heap.toNat 128 ≤ 2^64-1) :
    let result := UInt256.ofNat (allocateNext heap.toNat 64)
    let next := allocateNext heap.toNat 128
    MemoryPrefix mem (attestResultsMemory mem heap) heap.toNat ∧ heap.toNat ≤ result.toNat ∧
      result.toNat+64 = next ∧ next ≤ (attestResultsMemory mem heap).size ∧
      memLoad result (attestResultsMemory mem heap) = ⟨0⟩ ∧
      memLoad (UInt256.ofNat 64) (attestResultsMemory mem heap) = UInt256.ofNat next := by
  dsimp only
  have h64 : allocateNext heap.toNat 64 = heap.toNat+64 := fixedAllocation_next .bytes64 hh
  have h128 := allocateNext_128 hh
  have hf : allocateNext heap.toNat 64 ≤ 2^64-1 := by rw [h64]; rw [h128] at hn; omega
  have hr : (UInt256.ofNat (allocateNext heap.toNat 64)).toNat = allocateNext heap.toNat 64 :=
    ulit_toNat' _ (by change _ < 2^256; omega)
  have he : allocateNext (allocateNext heap.toNat 64) 64 = allocateNext heap.toNat 128 := by
    have h : allocateNext (allocateNext heap.toNat 64) 64 = allocateNext heap.toNat 64+64 := fixedAllocation_next .bytes64 hf
    rw [h,h64,h128]
  have hc := defaultResultMemory_covers (defaultResultMemory mem heap) (UInt256.ofNat (allocateNext heap.toNat 64))
  rw [hr] at hc
  refine ⟨(defaultResultMemory_prefix mem heap).trans
    ((defaultResultMemory_prefix (defaultResultMemory mem heap) (UInt256.ofNat (allocateNext heap.toNat 64))).mono (by rw [hr,h64]; omega)),?_,?_,?_,defaultResultMemory_used _ _,?_⟩
  · rw [hr,h64]; omega
  · rw [hr,h64,h128]
  · have heq : allocateNext heap.toNat 64+64 = allocateNext heap.toNat 128 := by rw [h64,h128]
    rw [heq] at hc
    exact hc
  · have h := defaultResultMemory_heap (defaultResultMemory mem heap) (UInt256.ofNat (allocateNext heap.toNat 64))
      (by rw [hr,h64]; omega)
    simpa only [hr,he] using h

end Benchmarks.EAS.EAS
