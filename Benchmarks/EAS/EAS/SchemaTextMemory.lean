import Benchmarks.EAS.EAS.SchemaText
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem schemaTextMemory_views (mem : ByteArray) (text heap record len : UInt256)
    (hlo : 96 ≤ record.toNat) (hdisj : record.toNat+128 ≤ heap.toNat)
    (hh : heap.toNat ≤ 2^64-1) (hl : len.toNat ≤ 2^64-1) :
    MemoryPrefix mem (schemaTextMemory mem text heap record len) (record.toNat+96) ∧
    memLoad (UInt256.ofNat 64) (schemaTextMemory mem text heap record len) =
      UInt256.ofNat (allocateNext heap.toNat (bytesAllocation len.toNat)) ∧
    record.toNat+128 ≤ (schemaTextMemory mem text heap record len).size := by
  let next := UInt256.ofNat (allocateNext heap.toNat (bytesAllocation len.toNat))
  let m1 := Reasoning.Theory.writeWord mem 64 next
  let m2 := Reasoning.Theory.writeWord m1 heap.toNat len
  let m3 := easCopyWords (text+UInt256.ofNat 32) (heap+UInt256.ofNat 32) m2 0 ((len.toNat+31)/32)
  let m4 := Reasoning.Theory.writeWord m3 (len+(heap+UInt256.ofNat 32)).toNat ⟨0⟩
  have hd : (heap+UInt256.ofNat 32).toNat = heap.toNat+32 :=
    uadd_word_ofNat_toNat heap 32 (by change heap.toNat+32 < 2^256; omega)
  have hz : (len+(heap+UInt256.ofNat 32)).toNat = heap.toNat+32+len.toNat := by
    rw [uadd_toNat,hd,Nat.mod_eq_of_lt (by change len.toNat+(heap.toNat+32) < 2^256; omega)]
    omega
  have hr : (record+UInt256.ofNat 96).toNat = record.toNat+96 :=
    uadd_word_ofNat_toNat record 96 (by change record.toNat+96 < 2^256; omega)
  have hb : (heap+UInt256.ofNat 32).toNat+0+32*((len.toNat+31)/32) < UInt256.size := by
    rw [hd]; change heap.toNat+32+0+32*((len.toNat+31)/32) < 2^256; omega
  have hp1 : MemoryPrefix mem m1 (record.toNat+96) :=
    memoryPrefix_sparse_writeWord _ _ _ _ (Or.inr (by decide))
  have hp2 : MemoryPrefix mem m2 (record.toNat+96) := hp1.trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega)))
  have hp3 : MemoryPrefix mem m3 (record.toNat+96) := hp2.trans
    (easCopyWords_prefix _ _ _ _ _ _ hb (by rw [hd]; omega))
  have hp4 : MemoryPrefix mem m4 (record.toNat+96) := hp3.trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by rw [hz]; omega)))
  have hsize2 : 96 ≤ m2.size := by simp only [m2,m1,writeWord_sparse_size]; omega
  have hsize3 : 96 ≤ m3.size := le_trans hsize2 (easCopyWords_size _ _ _ _ _)
  have hsize4 : 96 ≤ m4.size := by simp only [m4,writeWord_sparse_size]; omega
  constructor
  · exact hp4.trans (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by rw [hr])))
  constructor
  · apply mloadWordValue_of_readWithPadding
    · change 64 < (Reasoning.Theory.writeWord m4 (record+UInt256.ofNat 96).toNat heap).size
      rw [writeWord_sparse_size]; omega
    · change (Reasoning.Theory.writeWord m4 (record+UInt256.ofNat 96).toNat heap).readWithPadding 64 32 = next.toByteArray
      rw [writeWord_read_below_len _ _ _ _ _ (by rw [hr]; omega) hsize4]
      change (Reasoning.Theory.writeWord m3 (len+(heap+UInt256.ofNat 32)).toNat ⟨0⟩).readWithPadding 64 32 = _
      rw [writeWord_read_below_len _ _ _ _ _ (by rw [hz]; omega) hsize3]
      rw [easCopyWords_preserveRead _ _ _ _ _ 64 32 hb (by rw [hd]; omega) hsize2]
      change (Reasoning.Theory.writeWord m1 heap.toNat len).readWithPadding 64 32 = _
      rw [writeWord_read_below_len _ _ _ _ _ (by omega) (by simp only [m1,writeWord_sparse_size]; omega)]
      exact writeWord_sparse_read_back mem 64 next
  · change record.toNat+128 ≤ (Reasoning.Theory.writeWord m4 (record+UInt256.ofNat 96).toNat heap).size
    rw [writeWord_sparse_size,hr]
    omega

end Benchmarks.EAS.EAS
