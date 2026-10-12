import Benchmarks.EAS.EAS.TryRecoverExpr
import Benchmarks.EAS.EAS.EcrecoverOutput
import Benchmarks.EAS.EAS.RecordUID
import Benchmarks.EAS.EAS.RuntimeBlocks_053
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: a covered word below a word sequence keeps its loaded value.
theorem writeWordSequence_load_below (mem : ByteArray) (off : Nat) (ptr : UInt256) (ws : List UInt256)
    (hlo : ptr.toNat+32 ≤ off) (hin : ptr.toNat+32 ≤ mem.size) :
    memLoad ptr (writeWordSequence mem off ws) = memLoad ptr mem := by
  induction ws generalizing mem off with
  | nil => rfl
  | cons w ws ih =>
    rw [writeWordSequence,ih _ _ (by omega) (by rw [writeWord_sparse_size]; omega),
      memLoad_write_below mem off ptr w hlo hin]

-- LIBRARY CANDIDATE: an empty call result leaves output memory unchanged.
theorem callOutputMem_empty (mem : ByteArray) (off size : UInt256) :
    callOutputMem mem ByteArray.empty off size = mem := by
  unfold callOutputMem
  have hmin : min size (UInt256.ofNat ByteArray.empty.size) = ⟨0⟩  := by
    have hle : (⟨0⟩ : UInt256) ≤ size := by change 0 ≤ size.toNat; omega
    change min size (⟨0⟩ : UInt256) = ⟨0⟩
    change (if size ≤ (⟨0⟩ : UInt256) then size else ⟨0⟩) = ⟨0⟩
    split
    · apply u256_inj
      change size.toNat = 0
      have hz : size.toNat ≤ 0 := ‹size ≤ (⟨0⟩ : UInt256)›
      omega
    · rfl
  rw [hmin]
  exact byteArray_write_len_zero _ _ _ _

-- LIBRARY CANDIDATE: a complete returned word is an ordinary word write.
theorem callOutputMem_word (mem : ByteArray) (off w : UInt256) :
    callOutputMem mem w.toByteArray off ⟨32⟩ = Reasoning.Theory.writeWord mem off.toNat w := by
  unfold callOutputMem
  rw [callOutputLen32 (by rw [toByteArray_size]; decide),toByteArray_size,Nat.min_self]
  rfl

def tryRecoverInputMemory (mem : ByteArray) (heap hash v r s : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (writeWordSequence mem heap.toNat [hash,v,r,s]) 0 ⟨0⟩

theorem tryRecoverInputMemory_covers (mem : ByteArray) (heap hash v r s : UInt256) :
    heap.toNat+128 ≤ (tryRecoverInputMemory mem heap hash v r s).size := by
  have h := writeWordSequence_covers mem heap.toNat [hash,v,r,s] (by simp only [ne_eq,List.cons_ne_nil,not_false_eq_true])
  simp only [List.length_cons,List.length_nil] at h
  rw [tryRecoverInputMemory,writeWord_sparse_size]
  omega

theorem tryRecoverInputMemory_read {mem : ByteArray} {heap hash v r s : UInt256}
    (hlo : 96 ≤ heap.toNat) :
    (tryRecoverInputMemory mem heap hash v r s).readWithPadding heap.toNat 128 = tryRecoverPayload hash v r s := by
  have hc := writeWordSequence_covers mem heap.toNat [hash,v,r,s] (by simp only [ne_eq,List.cons_ne_nil,not_false_eq_true])
  simp only [List.length_cons,List.length_nil] at hc
  rw [tryRecoverInputMemory]
  change ((⟨0⟩ : UInt256).toByteArray.write 0 (writeWordSequence mem heap.toNat [hash,v,r,s]) 0 32).readWithPadding _ _ = _
  rw [write32_read_above_len _ _ 0 heap.toNat 128 (by rw [toByteArray_size])
    (Nat.zero_le _) (by omega) (by omega) (by decide) (by decide)]
  exact writeWordSequence_read mem heap.toNat [hash,v,r,s]

theorem tryRecoverInputMemory_prefix (mem : ByteArray) (heap hash v r s : UInt256) :
    MemoryPrefix mem (tryRecoverInputMemory mem heap hash v r s) heap.toNat :=
  (writeWordSequence_prefix mem heap.toNat heap.toNat [hash,v,r,s] (le_refl _)).trans
    (memoryPrefix_sparse_writeWord _ 0 heap.toNat ⟨0⟩ (Or.inr (by decide)))

theorem tryRecoverInputMemory_free {mem : ByteArray} {heap hash v r s : UInt256}
    (hlo : 96 ≤ heap.toNat) (hmem : 96 ≤ mem.size) (hh : memLoad ⟨64⟩ mem = heap) :
    memLoad ⟨64⟩ (tryRecoverInputMemory mem heap hash v r s) = heap := by
  have hc := writeWordSequence_grows mem heap.toNat [hash,v,r,s]
  rw [tryRecoverInputMemory,memLoad_write_above _ 0 ⟨64⟩ ⟨0⟩ (by decide)
    (by change 96 ≤ _; omega),writeWordSequence_load_below mem heap.toNat ⟨64⟩ [hash,v,r,s] hlo hmem]
  exact hh

theorem tryRecoverInputMemory_eq {mem : ByteArray} {heap hash v r s : UInt256}
    (hh : memLoad (UInt256.ofNat 64) mem = heap) (hv : v.toNat < 2^8)
    (hb : heap.toNat+128 < UInt256.size) :
    easBlocks.eas_block_16685_memory (mem := mem) (x0 := hash) (x1 := v) (x2 := r) (x3 := s) =
      tryRecoverInputMemory mem heap hash v r s := by
  have hm : UInt256.land v (UInt256.ofNat 255) = v := u256LandMaskCleanOfToNat v _ (bits := 8) rfl hv
  have hn (n : Nat) (hn : n ≤ 128) : (heap+UInt256.ofNat n).toNat = heap.toNat+n :=
    uadd_word_ofNat_toNat heap n (by omega)
  simp only [easBlocks.eas_block_16685_memory,hh,hm,hn 32 (by decide),hn 64 (by decide),hn 96 (by decide)]
  rfl

theorem ecrecoverOutputMemory {mem : ByteArray} {out : ByteArray} {a : AccountAddress} {limit : Nat}
    (hs : (out = ByteArray.empty ∧ a = 0) ∨ out = (UInt256.ofNat a.val).toByteArray)
    (hz : memLoad ⟨0⟩ mem = ⟨0⟩) (hmem : 96 ≤ mem.size) :
    memLoad ⟨0⟩ (callOutputMem mem out ⟨0⟩ ⟨32⟩) = UInt256.ofNat a.val ∧
    MemoryPrefix mem (callOutputMem mem out ⟨0⟩ ⟨32⟩) limit ∧
    memLoad ⟨64⟩ (callOutputMem mem out ⟨0⟩ ⟨32⟩) = memLoad ⟨64⟩ mem := by
  rcases hs with ⟨rfl,rfl⟩ | rfl
  · rw [callOutputMem_empty]
    exact ⟨hz,MemoryPrefix.refl _ _,rfl⟩
  · rw [callOutputMem_word]
    refine ⟨?_,memoryPrefix_sparse_writeWord _ 0 limit _ (Or.inr (by decide)),?_⟩
    · apply mloadWordValue_of_readWithPadding (by change 0 < _; rw [writeWord_sparse_size]; omega)
      exact writeWord_sparse_read_back _ _ _
    · exact memLoad_write_above _ 0 ⟨64⟩ _ (by decide) hmem

end Benchmarks.EAS.EAS
