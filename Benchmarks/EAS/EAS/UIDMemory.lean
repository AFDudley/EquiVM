import Benchmarks.EAS.EAS.UIDHeadMemory
import Benchmarks.EAS.EAS.RecordMemory
import Benchmarks.EAS.EAS.CopyPreserve
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def uidCopyMemory (mem : ByteArray) (heap dataPtr : UInt256) (a : AttestationRecord) : ByteArray :=
  Reasoning.Theory.writeWord
    (easCopyWords (dataPtr+UInt256.ofNat 32) (heap+UInt256.ofNat 153)
      (uidHeadMemory mem (heap.toNat+32) a) 0 ((a.data.size+31)/32))
    (heap.toNat+153+a.data.size) ⟨0⟩

def uidMemory (mem : ByteArray) (heap dataPtr : UInt256) (a : AttestationRecord) (bump : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord
    (Reasoning.Theory.writeWord (uidCopyMemory mem heap dataPtr a) (heap.toNat+153+a.data.size)
      (UInt256.shiftLeft bump (UInt256.ofNat 224)))
    heap.toNat (UInt256.ofNat (125+a.data.size))

theorem uidCopyMemory_read (mem : ByteArray) (heap dataPtr : UInt256) (a : AttestationRecord)
    (hh : heap.toNat ≤ 2^64-1) (hlo : 96 ≤ dataPtr.toNat)
    (hdisj : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ heap.toNat)
    (hin : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ mem.size)
    (hdata : mem.readWithPadding (dataPtr.toNat+32) a.data.size = a.data) :
    (uidCopyMemory mem heap dataPtr a).readWithPadding (heap.toNat+32) (121+a.data.size) =
      uidHeadBytes a ++ a.data := by
  let head := uidHeadMemory mem (heap.toNat+32) a
  let copied := easCopyWords (dataPtr+UInt256.ofNat 32) (heap+UInt256.ofNat 153) head 0 ((a.data.size+31)/32)
  have hs : (dataPtr+UInt256.ofNat 32).toNat = dataPtr.toNat+32 := uadd_word_ofNat_toNat dataPtr 32 (by change dataPtr.toNat+32 < 2^256; omega)
  have hd : (heap+UInt256.ofNat 153).toNat = heap.toNat+153 := uadd_word_ofNat_toNat heap 153 (by change heap.toNat+153 < 2^256; omega)
  have hb : (heap+UInt256.ofNat 153).toNat+0+32*((a.data.size+31)/32) < UInt256.size := by
    rw [hd]; change heap.toNat+153+0+32*((a.data.size+31)/32) < 2^256; omega
  have hp := uidHeadMemory_prefix mem (heap.toNat+32) heap.toNat a (by omega)
  have hhead := uidHeadMemory_covers mem (heap.toNat+32) a
  have hin' : (dataPtr+UInt256.ofNat 32).toNat+32*((a.data.size+31)/32) ≤ head.size := by
    rw [hs]; have hm := hp.size; dsimp only [head]; omega
  have hcov : heap.toNat+153+32*((a.data.size+31)/32) ≤ copied.size := by
    dsimp only [copied]
    rw [easCopyWords_eq_sequence _ _ _ 0 _ (by rw [hs]; omega)
      (by rw [hs,hd]; omega) (by simpa only [Nat.add_zero] using hin') hb]
    have hv := writeWordSequence_covers_from head ((heap+UInt256.ofNat 153).toNat+0)
      (memoryWords head ((dataPtr+UInt256.ofNat 32).toNat+0) ((a.data.size+31)/32))
      (by rw [hd]; dsimp only [head]; omega)
    simpa only [hd,Nat.add_zero,memoryWords_length] using hv
  have hr : copied.readWithPadding (heap.toNat+153) a.data.size = a.data := by
    have hc := easCopyWords_read (dataPtr+UInt256.ofNat 32) (heap+UInt256.ofNat 153) head
      ((a.data.size+31)/32) a.data.size (by rw [hs]; omega) (by rw [hs,hd]; omega) hin'
      (by simpa only [Nat.add_zero] using hb) (by omega)
    rw [hs,hd] at hc
    rw [hc,memoryPrefix_read_prefix hp (dataPtr.toNat+32) ((a.data.size+31)/32) a.data.size
      (by omega) (by omega) (by omega) (by change dataPtr.toNat+32+32*((a.data.size+31)/32) < 2^256; omega) (by omega),hdata]
  have hhread : copied.readWithPadding (heap.toNat+32) 121 = uidHeadBytes a := by
    rw [easCopyWords_preserveRead _ _ _ _ _ _ _ hb (by rw [hd] <;> omega) (by dsimp only [head]; omega)]
    exact uidHeadMemory_read _ _ _
  have hfull : copied.readWithPadding (heap.toNat+32) (121+a.data.size) = uidHeadBytes a ++ a.data := by
    by_cases hz : a.data.size = 0
    · have he := byteArray_eq_empty_of_size_eq_zero a.data hz
      rw [hz,Nat.add_zero,hhread,he,ByteArray.append_empty]
    · rw [byteArray_readWithPadding_split_unbounded _ _ 121 a.data.size (by decide) (by omega) (by omega)]
      simpa only [Nat.add_assoc,Nat.reduceAdd,hhread] using congrArg (uidHeadBytes a ++ ·) hr
  change (Reasoning.Theory.writeWord copied (heap.toNat+153+a.data.size) ⟨0⟩).readWithPadding
    (heap.toNat+32) (121+a.data.size) = _
  rw [writeWord_read_below_len _ _ _ _ _ (by omega) (by omega)]
  exact hfull

theorem uidMemory_read (mem : ByteArray) (heap dataPtr : UInt256) (a : AttestationRecord) (bump : UInt256)
    (hh : heap.toNat ≤ 2^64-1) (hlo : 96 ≤ dataPtr.toNat)
    (hdisj : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ heap.toNat)
    (hin : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ mem.size)
    (hdata : mem.readWithPadding (dataPtr.toNat+32) a.data.size = a.data) :
    (uidMemory mem heap dataPtr a bump).readWithPadding (heap.toNat+32) (125+a.data.size) = getUIDPayload a bump := by
  have hr := uidCopyMemory_read mem heap dataPtr a hh hlo hdisj hin hdata
  have hc : heap.toNat+153+a.data.size+32 ≤ (uidCopyMemory mem heap dataPtr a).size := by
    simp only [uidCopyMemory,writeWord_sparse_size]; omega
  unfold uidMemory
  rw [writeWord_read_above_len _ _ _ _ _ (by omega) (by rw [writeWord_sparse_size]; omega)]
  have ha := writeWord_append_read (uidCopyMemory mem heap dataPtr a) (heap.toNat+32) (121+a.data.size) 4
    (UInt256.shiftLeft bump (UInt256.ofNat 224)) (by omega) (by decide) (by decide)
  rw [show (heap.toNat+32)+(121+a.data.size) = heap.toNat+153+a.data.size by omega,
    show 121+a.data.size+4 = 125+a.data.size by omega,hr] at ha
  rw [ha]
  have hb := shiftLeft_bytes_prefix bump 28 (by decide)
  simp only [Nat.reduceMul,Nat.reduceSub] at hb
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [byteArray_toList_eq,ByteArray.data_append,Array.toList_append] at hb ⊢
  rw [hb]
  simp only [getUIDPayload,uidHeadBytes,List.toList_toArray,byteArray_toList_eq]

theorem uidMemory_length (mem : ByteArray) (heap dataPtr : UInt256) (a : AttestationRecord) (bump : UInt256) :
    memLoad heap (uidMemory mem heap dataPtr a bump) = UInt256.ofNat (125+a.data.size) := by
  apply mloadWordValue_of_readWithPadding
  · simp only [uidMemory,writeWord_sparse_size]; omega
  · exact writeWord_sparse_read_back _ _ _

end Benchmarks.EAS.EAS
