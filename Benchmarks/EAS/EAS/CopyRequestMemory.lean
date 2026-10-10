import Benchmarks.EAS.EAS.CopyRequestBytesMemory
import Benchmarks.EAS.EAS.CopyRequestGuards
import Benchmarks.EAS.EAS.AllocateBounds
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem requestCopyFieldsMemory_load (mem cd : ByteArray) (src heap : UInt256) (i : Nat)
    (hi : i < 4) (hb : heap.toNat+128 < UInt256.size) :
    memLoad (heap+UInt256.ofNat (32*i)) (requestCopyFieldsMemory mem cd heap src) = requestCopyWord cd src (32*i) := by
  have hn : heap+UInt256.ofNat (32*i) = UInt256.ofNat (heap.toNat+32*i) := by
    apply u256_inj
    rw [uadd_word_ofNat_toNat _ _ (by omega),ulit_toNat' _ (by omega)]
  rw [hn]
  have h := writeWordSequence_load_index mem heap.toNat [calldataWord cd src.toNat,
    requestCopyWord cd src 32,requestCopyWord cd src 64,requestCopyWord cd src 96] i hi (by omega)
  interval_cases i <;> simpa only [requestCopyFieldsMemory,List.getElem_cons_zero,List.getElem_cons_succ,
    Nat.mul_zero,Nat.mul_one,Nat.reduceMul,requestCopyWord,
    show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,u256_add_zero] using h

theorem requestCopyMemory_views (mem cd : ByteArray) (src heap : UInt256)
    (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1) (hsize : cd.size < 2^255+4)
    (hd : requestDataValid cd src) (hv : copyRequestValid heap.toNat (requestDataRecord cd src).data.size) :
    let next := UInt256.ofNat (allocateNext heap.toNat 192)
    let final := requestCopyMemory mem cd src heap
    let finalHeap := copyRequestNext heap.toNat (requestDataRecord cd src).data.size
    MemoryPrefix mem final heap.toNat ∧
    AttestationRequestMemoryView final heap next (requestDataRecord cd src) ∧
    memLoad (UInt256.ofNat 64) final = UInt256.ofNat finalHeap ∧
    heap.toNat+192 ≤ finalHeap ∧
    next.toNat+32+32*(((requestDataRecord cd src).data.size+31)/32) = finalHeap ∧
    finalHeap ≤ final.size := by
  let next := UInt256.ofNat (allocateNext heap.toNat 192)
  let m1 := Reasoning.Theory.writeWord mem 64 next
  let m2 := requestCopyFieldsMemory m1 cd heap src
  let final := requestCopyMemory mem cd src heap
  let r := requestDataRecord cd src
  have hl : (requestDataLength cd src).toNat ≤ 2^64-1 := hd.2.2.2.1
  have hn : next.toNat = allocateNext heap.toNat 192 := ulit_toNat' _ (by have := hv.1.1; change _ < 2^256; omega)
  have ha : allocateNext heap.toNat 192 = heap.toNat+192 := fixedAllocation_next .bytes192 hh
  have hnext : next.toNat ≤ 2^64-1 := by rw [hn]; exact hv.1.1
  have hdisj : heap.toNat+192 ≤ next.toNat := by rw [hn,ha]
  have hpayload := calldataPayload_bounds (cd := cd) (start := requestDataTail cd src) hsize hl hd.2.2.2.2
  have hm := requestCopyBytesMemory_views m2 cd src (requestCopyWord cd src 128) next heap hlo hdisj hnext hl hpayload.1
  have hcover : heap.toNat+128 ≤ m2.size :=
    writeWordSequence_covers m1 heap.toNat [calldataWord cd src.toNat,
      requestCopyWord cd src 32,requestCopyWord cd src 64,requestCopyWord cd src 96] (by simp)
  have hb : heap.toNat+128 < UInt256.size := by change _ < 2^256; omega
  have keep (i : Nat) (hi : i < 4) : memLoad (heap+UInt256.ofNat (32*i)) final = requestCopyWord cd src (32*i) := by
    have hx : (heap+UInt256.ofNat (32*i)).toNat = heap.toNat+32*i := uadd_word_ofNat_toNat _ _ (by omega)
    exact (memLoad_of_prefix hm.1 _ (by rw [hx]; omega) (by rw [hx]; omega) (by rw [hx]; omega)).trans
      (requestCopyFieldsMemory_load m1 cd src heap i hi hb)
  have hkeep0 : memLoad heap final = calldataWord cd src.toNat := by
    simpa only [Nat.mul_zero,requestCopyWord,show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,u256_add_zero] using keep 0 (by decide)
  have hprefix : MemoryPrefix mem final heap.toNat :=
    ((memoryPrefix_sparse_writeWord mem 64 heap.toNat next (Or.inr (by decide))).trans
      (writeWordSequence_prefix m1 heap.toNat heap.toNat _ (le_refl _))).trans (hm.1.mono (by omega))
  have hs : r.data.size = (requestDataLength cd src).toNat := requestDataRecord_size cd src
  have hresult : AttestationRequestMemoryView final heap next r := by
    refine ⟨hlo,by omega,hm.2.1,?_,?_,?_,?_,?_,hm.2.2.2.2.1,hm.2.2.2.2.2.1,?_,?_⟩
    · rw [hs]
      exact hm.2.2.1
    · change UInt256.land solcAddrMask (memLoad heap final) = UInt256.ofNat (AccountAddress.ofNat (calldataWord cd src.toNat).toNat).toNat
      rw [hkeep0,accountAddress_ofNat_toNat_eq_mask,u256_ofNat_toNat]
    · change UInt256.land easUint64Mask (memLoad (heap+UInt256.ofNat 32) final) = requestCopyWord cd src 32
      rw [keep 1 (by decide),u256_land_comm]
      exact hd.2.1.2.1.symm
    · change UInt256.isZero (UInt256.isZero (memLoad (heap+UInt256.ofNat 64) final)) =
        (decide ((requestCopyWord cd src 64).toNat ≠ 0)).toUInt256
      rw [keep 2 (by decide)]
      have hc := hd.2.1.2.2.1
      exact hc.symm.trans (boolWord_from_nat _ ((boolWord_nat_iff _).mp ((boolWordClean_iff _).mp hc.symm))).symm
    · exact keep 3 (by decide)
    · rw [hs,u256_ofNat_toNat]
      exact hm.2.2.2.2.2.2.1
    · rw [hs]
      exact hm.2.2.2.2.2.2.2.trans hpayload.2
  have he : copyRequestNext heap.toNat r.data.size = next.toNat+32+32*((r.data.size+31)/32) := by
    unfold copyRequestNext
    rw [allocateNext_bytes hv.1.1 (by rw [hs]; exact hl),← hn]
    unfold bytesAllocation
    omega
  refine ⟨hprefix,hresult,?_,?_,he.symm,?_⟩
  · have hf := hm.2.2.2.1
    change memLoad (UInt256.ofNat 64) final = _ at hf
    rw [hn] at hf
    change memLoad (UInt256.ofNat 64) final = UInt256.ofNat (copyRequestNext heap.toNat r.data.size)
    rw [copyRequestNext,hs]
    exact hf
  · rw [he]
    omega
  · rw [he]
    exact hresult.dataCovered

end Benchmarks.EAS.EAS
