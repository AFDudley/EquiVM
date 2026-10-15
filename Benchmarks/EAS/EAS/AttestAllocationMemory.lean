import Benchmarks.EAS.EAS.AttestRegisters
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- Memory after the result objects and the compiler's result register are initialized.
def attestAllocationMemory (kind : AttestCallKind) (mem : ByteArray) (heap data attester : UInt256) : ByteArray :=
  attestResultRegisterMemory kind (attestResultsMemory (attestEntryMemory kind mem data attester) heap)
    (UInt256.ofNat (allocateNext heap.toNat 64))

theorem attestAllocationMemory_facts (kind : AttestCallKind) (mem : ByteArray) (heap data attester : UInt256)
    (hc : 224 ≤ mem.size) (hd : 224 ≤ data.toNat) (hdi : data.toNat+32 ≤ mem.size)
    (hspan : data.toNat+32 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hf : memLoad (UInt256.ofNat 64) mem = heap) (hz : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hnext : allocateNext heap.toNat 128 ≤ 2^64-1) :
    let result := UInt256.ofNat (allocateNext heap.toNat 64)
    let uid := UInt256.ofNat (allocateNext heap.toNat 128)
    let m := attestAllocationMemory kind mem heap data attester
    mem.size ≤ m.size ∧ heap.toNat ≤ result.toNat ∧ result.toNat+64 = uid.toNat ∧ uid.toNat ≤ m.size ∧
      memLoad (UInt256.ofNat 64) m = uid ∧ memLoad (UInt256.ofNat 96) m = ⟨0⟩ ∧ memLoad result m = ⟨0⟩ ∧
      (kind = .many → memLoad (UInt256.ofNat 128) m = result ∧
        memLoad (UInt256.ofNat 160) m = attester ∧ memLoad (UInt256.ofNat 192) m = data) := by
  dsimp only
  obtain ⟨hsize0,hfree0,hzero0,hdata0,hregs0⟩ := attestEntryMemory_facts kind mem data attester heap hc hd hdi hf hz
  obtain ⟨hp,hrlo,hrend,hcover,hused,hfree⟩ := attestResultsMemory_view (attestEntryMemory kind mem data attester) heap (by omega) hh hnext
  have hn : (UInt256.ofNat (allocateNext heap.toNat 128)).toNat = allocateNext heap.toNat 128 :=
    ulit_toNat' _ (by change _ < 2^256; omega)
  have hm : 224 ≤ (attestResultsMemory (attestEntryMemory kind mem data attester) heap).size := by have := hp.size; omega
  have hz1 : memLoad (UInt256.ofNat 96) (attestResultsMemory (attestEntryMemory kind mem data attester) heap) = ⟨0⟩ :=
    (memLoad_of_prefix hp (UInt256.ofNat 96) (by decide) (by change 128 ≤ heap.toNat; omega)
      (by change 128 ≤ (attestEntryMemory kind mem data attester).size; omega)).trans hzero0
  have hregs1 : kind = .many →
      memLoad (UInt256.ofNat 160) (attestResultsMemory (attestEntryMemory kind mem data attester) heap) = attester ∧
      memLoad (UInt256.ofNat 192) (attestResultsMemory (attestEntryMemory kind mem data attester) heap) = data := by
    intro hk
    exact ⟨(memLoad_of_prefix hp (UInt256.ofNat 160) (by decide) (by change 192 ≤ heap.toNat; omega)
      (by change 192 ≤ (attestEntryMemory kind mem data attester).size; omega)).trans (hregs0 hk).1,
      (memLoad_of_prefix hp (UInt256.ofNat 192) (by decide) (by change 224 ≤ heap.toNat; omega)
      (by change 224 ≤ (attestEntryMemory kind mem data attester).size; omega)).trans (hregs0 hk).2⟩
  obtain ⟨hsize2,hfree2,hzero2,hused2,hregs2⟩ := attestResultRegisterMemory_facts kind
    (attestResultsMemory (attestEntryMemory kind mem data attester) heap) (UInt256.ofNat (allocateNext heap.toNat 64))
    (UInt256.ofNat (allocateNext heap.toNat 128)) data attester hm (by omega) (by omega) hfree hz1 hused hregs1
  exact ⟨le_trans hsize0 (le_trans hp.size hsize2),hrlo,by rw [hn]; exact hrend,
    by rw [hn]; exact le_trans hcover hsize2,hfree2,hzero2,hused2,hregs2⟩

end Benchmarks.EAS.EAS
