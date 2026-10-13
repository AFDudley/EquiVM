import Benchmarks.EAS.EAS.CalldataBytesMemory
import Benchmarks.EAS.EAS.CopyRequestBytes
import Benchmarks.EAS.EAS.RequestMemory
import Benchmarks.EAS.EAS.RecordUID
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem requestCopyBytesMemory_eq (mem cd : ByteArray) (src off heap record : UInt256)
    (hh : heap.toNat ≤ 2^64-1) (hr : record.toNat ≤ heap.toNat)
    (hl : (calldataWord cd (src+off).toNat).toNat ≤ 2^64-1) :
    requestCopyBytesMemory mem cd src off heap record =
      Reasoning.Theory.writeWord
        (Reasoning.Theory.writeWord
          (calldataBytesMemory mem cd ((src+off)+⟨32⟩).toNat heap.toNat
            (calldataWord cd (src+off).toNat).toNat
            (UInt256.ofNat (allocateNext heap.toNat (bytesAllocation (calldataWord cd (src+off).toNat).toNat))))
          (record.toNat+128) heap)
        (record.toNat+160) (requestCopyWord cd src 160) := by
  let len := calldataWord cd (src+off).toNat
  change len.toNat ≤ 2^64-1 at hl
  have h32 : (heap+⟨32⟩).toNat = heap.toNat+32 := uadd_word_ofNat_toNat heap 32 (by change _ < 2^256; omega)
  have hz : ((heap+len)+⟨32⟩).toNat = heap.toNat+32+len.toNat := by
    rw [uadd_toNat,uadd_toNat]
    change ((heap.toNat+len.toNat)%2^256+32)%2^256 = _
    rw [Nat.mod_eq_of_lt (by omega : heap.toNat+len.toNat < 2^256),Nat.mod_eq_of_lt (by omega)]
    omega
  have h128 : (record+⟨128⟩).toNat = record.toNat+128 := uadd_word_ofNat_toNat record 128 (by change _ < 2^256; omega)
  have h160 : (record+⟨160⟩).toNat = record.toNat+160 := uadd_word_ofNat_toNat record 160 (by change _ < 2^256; omega)
  dsimp only [len] at hz
  simp only [requestCopyBytesMemory,requestCopyPayloadMemory,calldataBytesMemory,h32,hz,h128,h160,u256_ofNat_toNat]

theorem requestCopyBytesMemory_views (mem cd : ByteArray) (src off heap record : UInt256)
    (hlo : 96 ≤ record.toNat) (hr : record.toNat+192 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1)
    (hl : (calldataWord cd (src+off).toNat).toNat ≤ 2^64-1)
    (hsrc : (calldataWord cd (src+off).toNat).toNat=0 ∨
      ((src+off)+⟨32⟩).toNat+(calldataWord cd (src+off).toNat).toNat ≤ cd.size) :
    let final := requestCopyBytesMemory mem cd src off heap record
    let len := calldataWord cd (src+off).toNat
    MemoryPrefix mem final (record.toNat+128) ∧
    record.toNat+192 ≤ final.size ∧ heap.toNat+32+32*((len.toNat+31)/32) ≤ final.size ∧
    memLoad (UInt256.ofNat 64) final = UInt256.ofNat (allocateNext heap.toNat (bytesAllocation len.toNat)) ∧
    memLoad (record+UInt256.ofNat 128) final = heap ∧
    memLoad (record+UInt256.ofNat 160) final = requestCopyWord cd src 160 ∧
    memLoad heap final = len ∧
    final.readWithPadding (heap.toNat+32) len.toNat = cd.readBytes ((src+off)+⟨32⟩).toNat len.toNat := by
  let len := calldataWord cd (src+off).toNat
  let next := UInt256.ofNat (allocateNext heap.toNat (bytesAllocation len.toNat))
  let m := calldataBytesMemory mem cd ((src+off)+⟨32⟩).toNat heap.toNat len.toNat next
  let m1 := Reasoning.Theory.writeWord m (record.toNat+128) heap
  let m2 := Reasoning.Theory.writeWord m1 (record.toNat+160) (requestCopyWord cd src 160)
  have hm := calldataBytesMemory_views mem cd ((src+off)+⟨32⟩).toNat heap.toNat len.toNat next hsrc
    (by omega) (by change _ < 2^256; omega)
  have hsize : heap.toNat+32+32*((len.toNat+31)/32) ≤ m.size := hm.2.1
  have hs1 : m.size ≤ m1.size := byteArray_write_size_ge_base _ _ _ _ _
  have hs2 : m1.size ≤ m2.size := byteArray_write_size_ge_base _ _ _ _ _
  have h128 : (record+UInt256.ofNat 128).toNat = record.toNat+128 := uadd_word_ofNat_toNat record 128 (by change _ < 2^256; omega)
  have h160 : (record+UInt256.ofNat 160).toNat = record.toNat+160 := uadd_word_ofNat_toNat record 160 (by change _ < 2^256; omega)
  rw [requestCopyBytesMemory_eq mem cd src off heap record hh (by omega) hl]
  change MemoryPrefix mem m2 (record.toNat+128) ∧ record.toNat+192 ≤ m2.size ∧
    heap.toNat+32+32*((len.toNat+31)/32) ≤ m2.size ∧ memLoad (UInt256.ofNat 64) m2 = next ∧
    memLoad (record+UInt256.ofNat 128) m2 = heap ∧
    memLoad (record+UInt256.ofNat 160) m2 = requestCopyWord cd src 160 ∧
    memLoad heap m2 = len ∧ m2.readWithPadding (heap.toNat+32) len.toNat =
      cd.readBytes ((src+off)+⟨32⟩).toNat len.toNat
  refine ⟨((hm.1.mono (by omega)).trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (le_refl _)))).trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega))),by omega,by omega,?_,?_,?_,?_,?_⟩
  · change memLoad (UInt256.ofNat 64) m2 = next
    rw [memLoad_write_below _ _ _ _ (by change 64+32 ≤ _; omega) (by change 64+32 ≤ _; omega)]
    rw [memLoad_write_below _ _ _ _ (by change 64+32 ≤ _; omega) (by change 64+32 ≤ _; omega)]
    exact hm.2.2.1
  · change memLoad (record+UInt256.ofNat 128) m2 = heap
    rw [memLoad_write_below _ _ _ _ (by rw [h128]) (by rw [h128]; omega)]
    apply mloadWordValue_of_readWithPadding
    · rw [h128]; omega
    · rw [h128]
      exact writeWord_sparse_read_back m (record.toNat+128) heap
  · apply mloadWordValue_of_readWithPadding
    · rw [h160]; omega
    · rw [h160]
      exact writeWord_sparse_read_back m1 (record.toNat+160) (requestCopyWord cd src 160)
  · change memLoad heap m2 = len
    rw [memLoad_write_above _ _ _ _ (by omega) (by omega),
      memLoad_write_above _ _ _ _ (by omega) (by omega)]
    have he := hm.2.2.2.1
    simpa only [u256_ofNat_toNat] using he
  · change m2.readWithPadding (heap.toNat+32) len.toNat = _
    rw [writeWord_read_above_len _ _ _ _ _ (by omega) (by omega),
      writeWord_read_above_len _ _ _ _ _ (by omega) (by omega)]
    exact hm.2.2.2.2

end Benchmarks.EAS.EAS
