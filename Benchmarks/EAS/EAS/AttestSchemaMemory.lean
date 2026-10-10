import Benchmarks.EAS.EAS.AttestArrayMemory
import Benchmarks.EAS.EAS.AttestUIDMemory
import Benchmarks.EAS.EAS.AttestResultMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem attestUIDMemory_resultView {mem calldata : ByteArray} {result heap schema used : UInt256} {len : Nat}
    (hr : 96 ≤ result.toNat) (hs : result.toNat+64 ≤ heap.toNat)
    (hc : result.toNat+32 ≤ mem.size) (hu : memLoad result mem = used)
    (hh : heap.toNat ≤ 2^64-1) (hl : len ≤ 2^64-1) :
    AttestResultMemoryView (attestUIDMemory mem calldata result heap schema len) result heap
      (List.replicate len ⟨0⟩) used (allocateNext heap.toNat (32+32*len)) := by
  obtain ⟨hp,hcover,hfree,hptr,harray,hcall⟩ := attestUIDMemory_view mem calldata result heap schema len hr hs hh hl
  refine ⟨hr,hs,?_,(memLoad_of_prefix hp result hr (le_refl _) hc).trans hu,hptr,harray⟩
  have hn := allocateNext_wordArray hh hl
  rw [hn] at hcover
  omega

theorem attestSetupMemory_of_schema {before after : ByteArray} {site : UIDSite} {uidPtr : UInt256}
    {rs : List AttestationRequestRecord} {s : SchemaRecord} {attester : AccountAddress} {used : UInt256}
    {start heap : Nat}
    (hp : MemoryPrefix before after start) (hb : start < UInt256.size)
    (hu : 224 ≤ uidPtr.toNat)
    (hrequests : AttestationRequestArrayMemoryView before (attestRequestArrayPtr site before) rs uidPtr.toNat)
    (hresult : AttestResultMemoryView before (recordResultPtr site before) uidPtr (List.replicate rs.length ⟨0⟩) used start)
    (ha : recordCreateAttester site before = UInt256.ofNat attester.val)
    (hz : memLoad (UInt256.ofNat 96) before = ⟨0⟩)
    (hsv : SchemaMemoryView after (requestSchemaPtr site) s)
    (hsl : uidPtr.toNat+32+32*rs.length ≤ (requestSchemaPtr site).toNat)
    (hsh : (requestSchemaPtr site).toNat+128 ≤ heap) (hh : start ≤ heap) :
    AttestSetupMemory after site uidPtr rs s attester heap := by
  have hus := hresult.uids.span
  have huc := hresult.uids.covered
  simp only [List.length_replicate] at hus huc
  have hfoot : MemoryPrefix before after uidPtr.toNat := hp.mono (by omega)
  have hr := recordResultPtr_preserve site hfoot (by omega) (by omega)
  have hpointer : recordUIDsPtr site before = uidPtr := by cases site <;> exact hresult.uidPointer
  refine ⟨hu,?_,hsv,hsl,hsh,(hresult.uids.preserve hp hb).mono hh,?_,?_,?_,?_,?_,?_⟩
  · rw [attestRequestArrayPtr_preserve site hfoot hu (by omega)]
    exact hrequests.preserve hfoot uidPtr.val.isLt
  · exact (recordUIDsPtr_preserve site hfoot (by omega) (by omega) hresult.low hresult.span hresult.covered uidPtr.val.isLt).trans hpointer
  · rw [hr]; exact hresult.low
  · rw [hr]; exact hresult.span
  · rw [hr]; exact le_trans hresult.covered hp.size
  · exact (recordCreateAttester_preserve site hfoot (by omega) (by omega)).trans ha
  · exact (memLoad_of_prefix hp (UInt256.ofNat 96) (by decide) (by change 128 ≤ start; omega)
      (by change 128 ≤ before.size; omega)).trans hz

end Benchmarks.EAS.EAS
