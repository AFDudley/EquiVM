import Benchmarks.EAS.EAS.UIDMemory
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem uidMemory_prefix (mem : ByteArray) (heap dataPtr : UInt256) (a : AttestationRecord) (bump : UInt256)
    (hb : heap.toNat+153+32*((a.data.size+31)/32) < UInt256.size) :
    MemoryPrefix mem (uidMemory mem heap dataPtr a bump) heap.toNat := by
  have hd : (heap+UInt256.ofNat 153).toNat = heap.toNat+153 := uadd_word_ofNat_toNat heap 153 (by omega)
  have hp := uidHeadMemory_prefix mem (heap.toNat+32) heap.toNat a (by omega)
  have hp' := easCopyWords_prefix (dataPtr+UInt256.ofNat 32) (heap+UInt256.ofNat 153)
    (uidHeadMemory mem (heap.toNat+32) a) 0 ((a.data.size+31)/32) heap.toNat
    (by simpa only [hd,Nat.add_zero] using hb) (by rw [hd]; omega)
  exact hp.trans (hp'.trans ((memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega))).trans
    ((memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega))).trans
      (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (le_refl _))))))

theorem uidMemory_covers (mem : ByteArray) (heap dataPtr : UInt256) (a : AttestationRecord) (bump : UInt256) :
    heap.toNat+185+a.data.size ≤ (uidMemory mem heap dataPtr a bump).size := by
  simp only [uidMemory,uidCopyMemory,writeWord_sparse_size]
  omega

set_option maxHeartbeats 800000 in
theorem uidMemory_hash (mem : ByteArray) (heap dataPtr next : UInt256) (a : AttestationRecord) (bump : UInt256)
    (hh : heap.toNat ≤ 2^64-1) (hlo : 96 ≤ dataPtr.toNat)
    (hdisj : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ heap.toNat)
    (hin : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ mem.size)
    (hdata : mem.readWithPadding (dataPtr.toNat+32) a.data.size = a.data) :
    keccakWord (heap+UInt256.ofNat 32)
      (memLoad heap (Reasoning.Theory.writeWord (uidMemory mem heap dataPtr a bump) 64 next))
      (Reasoning.Theory.writeWord (uidMemory mem heap dataPtr a bump) 64 next) = getUIDWord a bump := by
  have hc := uidMemory_covers mem heap dataPtr a bump
  have hhlo : 96 ≤ heap.toNat := by omega
  have hs : (heap+UInt256.ofNat 32).toNat = heap.toNat+32 := uadd_word_ofNat_toNat heap 32 (by change heap.toNat+32 < 2^256; omega)
  have hlen : memLoad heap (Reasoning.Theory.writeWord (uidMemory mem heap dataPtr a bump) 64 next) = UInt256.ofNat (125+a.data.size) := by
    have hp := memoryPrefix_sparse_writeWord (uidMemory mem heap dataPtr a bump) 64 (heap.toNat+32) next (Or.inr (by decide))
    exact (memLoad_of_prefix hp heap hhlo (le_refl _) (by omega)).trans (uidMemory_length mem heap dataPtr a bump)
  rw [hlen]
  unfold keccakWord
  rw [hs,ulit_toNat' _ (by change 125+a.data.size < 2^256; omega)]
  rw [writeWord_read_above_len _ _ _ _ _ (by omega) (by omega),
    uidMemory_read mem heap dataPtr a bump hh hlo hdisj hin hdata]
  exact keccakSlot_eq _

end Benchmarks.EAS.EAS
