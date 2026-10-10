import Benchmarks.EAS.EAS.DefaultArrayRegions
import Benchmarks.EAS.EAS.AttestLoopMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

structure AttestSetupMemory (mem : ByteArray) (site : UIDSite) (uidPtr : UInt256)
    (rs : List AttestationRequestRecord) (s : SchemaRecord) (attester : AccountAddress) (heap : Nat) : Prop where
  uidLow : 224 ≤ uidPtr.toNat
  requests : AttestationRequestArrayMemoryView mem (attestRequestArrayPtr site mem) rs uidPtr.toNat
  schemaView : SchemaMemoryView mem (requestSchemaPtr site) s
  schemaLow : uidPtr.toNat+32+32*rs.length ≤ (requestSchemaPtr site).toNat
  schemaHigh : (requestSchemaPtr site).toNat+128 ≤ heap
  uidArray : WordArrayMemoryView mem uidPtr (List.replicate rs.length ⟨0⟩) heap
  uidPointer : recordUIDsPtr site mem = uidPtr
  resultLow : 96 ≤ (recordResultPtr site mem).toNat
  resultEnd : (recordResultPtr site mem).toNat+64 ≤ uidPtr.toNat
  resultCovered : (recordResultPtr site mem).toNat+64 ≤ mem.size
  attesterWord : recordCreateAttester site mem = UInt256.ofNat attester.val
  zero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩

def attestArraysMemory (mem calldata : ByteArray) (heap : UInt256) (len : Nat) : ByteArray :=
  wordArrayAllocationMemory (defaultArrayMemory mem heap len) calldata
    (UInt256.ofNat (allocateNext heap.toNat (32+352*len))) len

theorem attestArraysMemory_init {mem calldata : ByteArray} {site : UIDSite} {uidPtr heap t3 t4 : UInt256}
    {rs : List AttestationRequestRecord} {s : SchemaRecord} {attester : AccountAddress}
    (h : AttestSetupMemory mem site uidPtr rs s attester heap.toNat)
    (ha : recordArrayPtr site t3 t4 = heap)
    (hv : recordValuesPtr site t4 = UInt256.ofNat (allocateNext heap.toNat (32+352*rs.length)))
    (hh : heap.toNat ≤ 2^64-1) (hl : rs.length ≤ 2^64-1)
    (hr : allocateNext heap.toNat (32+352*rs.length) ≤ 2^64-1) :
    let next := allocateNext (allocateNext heap.toNat (32+352*rs.length)) (32+32*rs.length)
    MemoryPrefix mem (attestArraysMemory mem calldata heap rs.length) heap.toNat ∧
      AttestLoopMemory (attestArraysMemory mem calldata heap rs.length) site t3 t4 uidPtr rs s attester
        (defaultArrayPointers heap rs.length) (List.replicate rs.length ⟨0⟩) (List.replicate rs.length ⟨0⟩)
        (List.replicate rs.length defaultAttestationRecord) next := by
  dsimp only
  let middle := allocateNext heap.toNat (32+352*rs.length)
  let next := allocateNext middle (32+32*rs.length)
  let records := defaultArrayMemory mem heap rs.length
  let final := attestArraysMemory mem calldata heap rs.length
  change MemoryPrefix mem final heap.toNat ∧ AttestLoopMemory final site t3 t4 uidPtr rs s attester
    (defaultArrayPointers heap rs.length) (List.replicate rs.length ⟨0⟩) (List.replicate rs.length ⟨0⟩)
    (List.replicate rs.length defaultAttestationRecord) next
  have hu := h.uidLow
  have hus := h.uidArray.span
  have huc := h.uidArray.covered
  have hsh := h.schemaHigh
  have hsl := h.schemaLow
  simp only [List.length_replicate] at hus huc
  have hlo : 96 ≤ heap.toNat := by omega
  have hm : middle = heap.toNat+32+352*rs.length := allocateNext_recordArray hh hl
  have hn : next = middle+32+32*rs.length := allocateNext_wordArray hr hl
  have hmid : (UInt256.ofNat middle).toNat = middle := ulit_toNat' _ (by change middle < 2^256; omega)
  have hb : middle < UInt256.size := by change middle < 2^256; omega
  obtain ⟨hp1,hcover1,hfree1,hptrs⟩ := defaultArrayMemory_view mem heap rs.length hlo hh hl
  obtain ⟨hp2,hcover2,hlen2,hfree2,hvalues⟩ := wordArrayAllocationMemory_view records calldata
    (UInt256.ofNat middle) rs.length (by rw [hmid,hm]; omega) (by rw [hmid]; exact hr) hl
  simp only [hmid] at hp2 hcover2 hfree2 hvalues
  have hp : MemoryPrefix mem final heap.toNat := hp1.trans (hp2.mono (by rw [hm]; omega))
  have hfoot := hp.mono (show uidPtr.toNat ≤ heap.toNat by omega)
  have hsize : 224 ≤ mem.size := by omega
  have hresult := recordResultPtr_preserve site hfoot (by omega) (by omega)
  refine ⟨hp,hu,?_,h.schemaView.preserve hp hsh heap.val.isLt,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,hfree2⟩
  · rw [attestRequestArrayPtr_preserve site hfoot hu hsize]
    exact h.requests.preserve hfoot uidPtr.val.isLt
  · simpa only [List.length_replicate] using h.schemaLow
  · rw [ha]; exact h.schemaHigh
  · rw [ha]
    exact (hptrs.preserve hp2 hb).mono (by rw [hn]; omega)
  · rw [hv]; exact hvalues
  · rw [hv,hmid]; exact hcover2
  · exact (h.uidArray.preserve hp heap.val.isLt).mono (by rw [hn,hm]; omega)
  · rw [ha,hv,hmid,defaultArrayPointers_length,hm]; omega
  · exact defaultArrayPointers_length _ _
  · simp only [List.length_replicate,defaultArrayPointers_length]
  · simp only [List.length_replicate,defaultArrayPointers_length]
  · rw [ha,hv]
    have hregions := defaultArrayMemory_regions mem heap uidPtr (UInt256.ofNat middle) rs.length
      (by omega) hh hl (by omega) (by rw [hmid]) (by omega) h.zero
    exact hregions.preserve hp2 hb (by change uidPtr.toNat ≤ middle; rw [hm]; omega) (by rw [hn]; omega)
  · exact (recordUIDsPtr_preserve site hfoot (by omega) (by omega) h.resultLow h.resultEnd h.resultCovered uidPtr.val.isLt).trans h.uidPointer
  · rw [hresult]; exact h.resultLow
  · rw [hresult]; exact h.resultEnd
  · rw [hresult]; exact le_trans h.resultCovered hp.size
  · exact (recordCreateAttester_preserve site hfoot (by omega) (by omega)).trans h.attesterWord

end Benchmarks.EAS.EAS
