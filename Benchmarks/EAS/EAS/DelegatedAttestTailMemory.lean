import Benchmarks.EAS.EAS.DelegatedAttestPrepareMemory
import Benchmarks.EAS.EAS.OneRequestMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def delegatedAttestTailCopiedMemory (mem cd : ByteArray) (root heap : UInt256) : ByteArray :=
  requestCopyMemory (oneRequestArrayMemory mem heap) cd (delegatedAttestData cd root) (UInt256.ofNat (heap.toNat+256))
def delegatedAttestTailMemory (mem cd : ByteArray) (root heap : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (delegatedAttestTailCopiedMemory mem cd root heap) (heap.toNat+32) (UInt256.ofNat (heap.toNat+256))

theorem delegatedAttestTailMemory_view (mem cd : ByteArray) (root heap : UInt256)
    (hlo : 224 ≤ heap.toNat) (hh : heap.toNat+256 ≤ 2^64-1) (hcov : 128 ≤ mem.size)
    (hz : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hsize : cd.size < 2^255+4) (hd : requestDataValid cd (delegatedAttestData cd root))
    (hv : copyRequestValid (heap.toNat+256) (delegatedAttestRecord cd root).data.data.size) :
    let finalHeap := copyRequestNext (heap.toNat+256) (delegatedAttestRecord cd root).data.data.size
    (heap.toNat+64 ≤ (delegatedAttestTailCopiedMemory mem cd root heap).size ∧
      memLoad heap (delegatedAttestTailCopiedMemory mem cd root heap) = ⟨1⟩) ∧
    AttestationRequestArrayRegion (delegatedAttestTailMemory mem cd root heap) heap [(delegatedAttestRecord cd root).data] 224 finalHeap ∧
    memLoad (UInt256.ofNat 64) (delegatedAttestTailMemory mem cd root heap) = UInt256.ofNat finalHeap ∧
    memLoad (UInt256.ofNat 96) (delegatedAttestTailMemory mem cd root heap) = ⟨0⟩ := by
  let start := UInt256.ofNat (heap.toNat+256)
  let final := delegatedAttestTailCopiedMemory mem cd root heap
  have hn : start.toNat = heap.toNat+256 := ulit_toNat' _ (by change _ < 2^256; omega)
  have harray := oneRequestArrayMemory_views mem heap (by omega)
  have hcopy := requestCopyMemory_views (oneRequestArrayMemory mem heap) cd (delegatedAttestData cd root) start
    (by rw [hn]; omega) (by rw [hn]; exact hh) hsize hd (by simpa only [hn] using hv)
  simp only [hn] at hcopy
  have hc : heap.toNat+256 ≤ final.size := le_trans harray.2.1 hcopy.1.size
  have hlen : memLoad heap final = ⟨1⟩ :=
    (memLoad_of_prefix hcopy.1 _ (by omega) (by omega) (by have := harray.2.1; omega)).trans harray.2.2.2
  have hz1 : memLoad (UInt256.ofNat 96) (oneRequestArrayMemory mem heap) = ⟨0⟩ :=
    (memLoad_of_prefix harray.1 (UInt256.ofNat 96) (by decide) (by change 128 ≤ heap.toNat; omega) hcov).trans hz
  have hz2 : memLoad (UInt256.ofNat 96) final = ⟨0⟩ :=
    (memLoad_of_prefix hcopy.1 _ (by decide) (by change 128 ≤ heap.toNat+256; omega)
      (by have := harray.2.1; change 128 ≤ _; omega)).trans hz1
  have hb : copyRequestNext (heap.toNat+256) (delegatedAttestRecord cd root).data.data.size < UInt256.size := by
    have := hv.2.2.1; change _ < 2^256; omega
  have hnext : (UInt256.ofNat (allocateNext (heap.toNat+256) 192)).toNat = heap.toNat+256+192 := by
    have hnext := fixedAllocation_next .bytes192 hh
    change allocateNext (heap.toNat+256) 192 = heap.toNat+256+192 at hnext
    rw [hnext]
    exact ulit_toNat' _ (by change _ < 2^256; omega)
  have hreg := requestSingleton_set (array := heap) (lower := 224) (by omega) hlo
    (by rw [hn]; omega) (by rw [hnext]; omega) (by omega) hlen hcopy.2.1 (by simpa only [hn] using hcopy.2.2.2.1)
    (le_of_eq hcopy.2.2.2.2.1) hb
  exact ⟨⟨by change heap.toNat+64 ≤ final.size; omega,hlen⟩,hreg,
    (memLoad_write_below final (heap.toNat+32) (UInt256.ofNat 64) start (by change 96 ≤ _; omega)
      (by change 96 ≤ final.size; omega)).trans hcopy.2.2.1,
    (memLoad_write_below final (heap.toNat+32) (UInt256.ofNat 96) start (by change 128 ≤ _; omega)
      (by change 128 ≤ final.size; omega)).trans hz2⟩

end Benchmarks.EAS.EAS
