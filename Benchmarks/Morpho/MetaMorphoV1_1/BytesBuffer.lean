import Benchmarks.Morpho.MetaMorphoV1_1.ByteMemoryPrefix

/-! A raw-call byte buffer needs only its actual payload to be materialized in sparse memory. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

structure BytesBuffer (mem : ByteArray) (ptr : UInt256) (bytes : ByteArray) : Prop where
  size : ptr.toNat + 32 + bytes.size ≤ mem.size
  length : memLoad ptr mem = UInt256.ofNat bytes.size
  data : mem.readWithPadding (ptr.toNat + 32) bytes.size = bytes

theorem BytesBuffer.preserve {before after bytes : ByteArray} {ptr : UInt256} {limit : Nat}
    (buffer : BytesBuffer before ptr bytes) (h : ByteMemoryPrefix before after limit)
    (hlo : 96 ≤ ptr.toNat) (hlimit : ptr.toNat + 32 + bytes.size ≤ limit) :
    BytesBuffer after ptr bytes := by
  refine ⟨le_trans buffer.size h.size, ?_, ?_⟩
  · have hp := h.words.load_preserved hlo (by omega) (by have := buffer.size; omega) ptr.val.isLt
    simp only [u256_ofNat_toNat] at hp
    exact hp.trans buffer.length
  · rw [h.read _ _ (by omega) hlimit buffer.size, buffer.data]

theorem BytesBuffer.writeWord {mem bytes : ByteArray} {ptr : UInt256}
    (buffer : BytesBuffer mem ptr bytes) (off : Nat) (word : UInt256)
    (hdisj : ptr.toNat + 32 + bytes.size ≤ off ∨ off + 32 ≤ ptr.toNat) :
    BytesBuffer (writeWord mem off word) ptr bytes := by
  refine ⟨by rw [writeWord_sparse_size]; have := buffer.size; omega, ?_, ?_⟩
  · unfold memLoad
    have hin := buffer.size
    rw [if_neg (by rw [writeWord_sparse_size]; omega),
      writeWord_sparse_read_preserved _ _ _ _
        (hdisj.imp (fun h ↦ ⟨by omega, by omega⟩) (fun h ↦ ⟨h, by omega⟩))]
    simpa only [memLoad, if_neg (show ¬ ptr.toNat ≥ mem.size by omega)] using buffer.length
  · rw [writeWord_sparse_read_preserved_unbounded _ _ _ _ _ buffer.size
      (hdisj.imp (fun h ↦ h) (fun h ↦ by omega)), buffer.data]

theorem callReturnMemory_buffer (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hmem : 128 ≤ mem.size) (hzero : memLoad ⟨96⟩ mem = ⟨0⟩) :
    BytesBuffer (callReturnMemory mem ptr out) (callReturnPointer ptr out) out := by
  refine ⟨?_, callReturnMemory_length mem ptr out hzero, ?_⟩
  · unfold callReturnMemory callReturnPointer
    split
    · simpa only [‹out.size = 0›] using hmem
    · rw [bytesAllocMem_size mem ptr out ‹_›]; omega
  · by_cases hz : out.size = 0
    · rw [hz, byteArray_readWithPadding_zero]
      apply ByteArray.ext
      exact (Array.eq_empty_of_size_eq_zero hz).symm
    · simp only [callReturnMemory, callReturnPointer, hz, if_false]
      have hs := bytesAllocMem_size mem ptr out hz
      rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega) (by rw [hs]; omega)]
      unfold bytesAllocMem
      have hc := copyWindow_extract out
        (writeWord (writeWord mem 64 (bytesAllocPtr ptr out.size)) ptr.toNat
          (UInt256.ofNat out.size)) 0 (ptr.toNat + 32) out.size 0 out.size hz
          (by omega) (by simp only [writeWord_sparse_size]; omega) (by omega)
      simpa only [Nat.add_zero, Nat.zero_add, byteArray_extract_self] using hc

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
