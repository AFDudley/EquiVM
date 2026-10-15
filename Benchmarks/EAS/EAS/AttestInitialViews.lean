import Benchmarks.EAS.EAS.AttestInitialEVM
import Benchmarks.EAS.EAS.AttestSchemaRun
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem attestInitialMemory_view (kind : AttestCallKind) (mem calldata : ByteArray) (heap data schema : UInt256)
    (attester : AccountAddress) (rs : List AttestationRequestRecord)
    (hlo : 224 ≤ data.toNat) (hspan : data.toNat+32 ≤ heap.toNat) (hcovered : data.toNat+32 ≤ mem.size)
    (hh : heap.toNat ≤ 2^64-1) (hheap : memLoad (UInt256.ofNat 64) mem = heap)
    (hzero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hg : allocateNext heap.toNat 128 ≤ 2^64-1) (hl : rs.length ≤ 2^64-1)
    (hdata : AttestationRequestArrayMemoryView
      (attestAllocationMemory kind mem heap data (UInt256.ofNat attester.val)) data rs heap.toNat) :
    let uid := UInt256.ofNat (allocateNext heap.toNat 128)
    let result := UInt256.ofNat (allocateNext heap.toNat 64)
    let next := allocateNext (allocateNext heap.toNat 128) (32+32*rs.length)
    let m := attestInitialMemory kind mem calldata heap data (UInt256.ofNat attester.val) schema rs.length
    MemoryPrefix (attestAllocationMemory kind mem heap data (UInt256.ofNat attester.val)) m heap.toNat ∧
      AttestationRequestArrayMemoryView m data rs uid.toNat ∧
      AttestResultMemoryView m result uid (List.replicate rs.length ⟨0⟩) ⟨0⟩ next ∧
      224 ≤ uid.toNat ∧ 160 ≤ result.toNat ∧ heap.toNat ≤ result.toNat ∧
      (kind = .many → memLoad (UInt256.ofNat 128) m = result ∧
        memLoad (UInt256.ofNat 160) m = UInt256.ofNat attester.val ∧ memLoad (UInt256.ofNat 192) m = data) ∧
      memLoad (UInt256.ofNat 96) m = ⟨0⟩ ∧ next ≤ m.size ∧
      m.readWithPadding next 36 = getSchemaPayload schema := by
  dsimp only
  obtain ⟨hsize,hrlo,hrspan,huidcover,hfree,hzero',hused,hregs⟩ :=
    attestAllocationMemory_facts kind mem heap data (UInt256.ofNat attester.val)
      (by omega) hlo hcovered hspan hh hheap hzero hg
  have hu : (UInt256.ofNat (allocateNext heap.toNat 128)).toNat = allocateNext heap.toNat 128 :=
    ulit_toNat' _ (by change _ < 2^256; omega)
  have hr : 96 ≤ (UInt256.ofNat (allocateNext heap.toNat 64)).toNat := by omega
  obtain ⟨hp,hsize',hfree',huid,harray,hpayload⟩ := attestUIDMemory_view
    (attestAllocationMemory kind mem heap data (UInt256.ofNat attester.val)) calldata
    (UInt256.ofNat (allocateNext heap.toNat 64)) (UInt256.ofNat (allocateNext heap.toNat 128)) schema rs.length
    hr (le_of_eq hrspan) (by rw [hu]; exact hg) hl
  have hv := attestUIDMemory_resultView (calldata := calldata) (schema := schema) (len := rs.length) hr (le_of_eq hrspan) (by omega) hused (by rw [hu]; exact hg) hl
  rw [hu] at hsize' hfree' harray hpayload hv
  have hprefix := hp.mono (show heap.toNat ≤ (UInt256.ofNat (allocateNext heap.toNat 64)).toNat+32 by omega)
  have hregs' : kind = .many →
      memLoad (UInt256.ofNat 128) (attestInitialMemory kind mem calldata heap data (UInt256.ofNat attester.val) schema rs.length) = UInt256.ofNat (allocateNext heap.toNat 64) ∧
      memLoad (UInt256.ofNat 160) (attestInitialMemory kind mem calldata heap data (UInt256.ofNat attester.val) schema rs.length) = UInt256.ofNat attester.val ∧
      memLoad (UInt256.ofNat 192) (attestInitialMemory kind mem calldata heap data (UInt256.ofNat attester.val) schema rs.length) = data := by
    intro hk
    have hm : 224 ≤ (attestAllocationMemory kind mem heap data (UInt256.ofNat attester.val)).size := by omega
    exact ⟨(memLoad_of_prefix hprefix (UInt256.ofNat 128) (by decide) (by change 160 ≤ heap.toNat; omega)
        (by change 160 ≤ _; omega)).trans (hregs hk).1,
      (memLoad_of_prefix hprefix (UInt256.ofNat 160) (by decide) (by change 192 ≤ heap.toNat; omega)
        (by change 192 ≤ _; omega)).trans (hregs hk).2.1,
      (memLoad_of_prefix hprefix (UInt256.ofNat 192) (by decide) (by change 224 ≤ heap.toNat; omega)
        hm).trans (hregs hk).2.2⟩
  exact ⟨hprefix,(hdata.preserve hprefix heap.val.isLt).mono (by omega),hv,by omega,by omega,hrlo,hregs',
    (memLoad_of_prefix hprefix (UInt256.ofNat 96) (by decide) (by change 128 ≤ heap.toNat; omega)
      (by change 128 ≤ _; omega)).trans hzero',by unfold attestInitialMemory; omega,hpayload⟩

end Benchmarks.EAS.EAS
