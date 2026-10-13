import Benchmarks.EAS.EAS.TypedDataMemory
import Benchmarks.EAS.EAS.GetAttestationEVM
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def verifyBuffer (mem : ByteArray) (heap : Nat) (ws : List UInt256) : ByteArray :=
  Reasoning.Theory.writeWord
    (Reasoning.Theory.writeWord (writeWordSequence mem (heap+32) ws) heap (UInt256.ofNat (32*ws.length)))
    64 (UInt256.ofNat (allocateNext heap (32+32*ws.length)))

theorem verifyBuffer_covers (mem : ByteArray) (heap : Nat) (ws : List UInt256) (hne : ws ≠ []) :
    heap+32+32*ws.length ≤ (verifyBuffer mem heap ws).size := by
  have h := writeWordSequence_covers mem (heap+32) ws hne
  simp only [verifyBuffer,writeWord_sparse_size]
  omega

theorem verifyBuffer_payload (mem : ByteArray) (heap : Nat) (ws : List UInt256)
    (hlo : 96 ≤ heap) (hne : ws ≠ []) (hlen : ws.length ≤ 8) :
    (verifyBuffer mem heap ws).readWithPadding (heap+32) (32*ws.length) = wordBytes ws := by
  have hc := writeWordSequence_covers mem (heap+32) ws hne
  have hu := lt_usize 256 (by decide)
  have hpos : 0 < ws.length := by cases ws with | nil => contradiction | cons a xs => simp only [List.length_cons]; omega
  rw [verifyBuffer,writeWord_read_preserved_len _ 64 (heap+32) (32*ws.length) _
    (by rw [writeWord_sparse_size]; omega) (Or.inr ⟨by omega,by rw [writeWord_sparse_size]; omega⟩)
    (by omega) (by omega)]
  rw [writeWord_read_preserved_len _ heap (heap+32) (32*ws.length) _
    (by omega) (Or.inr ⟨by omega,by omega⟩) (by omega) (by omega)]
  exact writeWordSequence_read mem (heap+32) ws

theorem verifyBuffer_header (mem : ByteArray) (heap : Nat) (ws : List UInt256) (hlo : 96 ≤ heap) :
    (verifyBuffer mem heap ws).readWithPadding heap 32 = (UInt256.ofNat (32*ws.length)).toByteArray := by
  rw [verifyBuffer,writeWord_sparse_read_preserved _ 64 heap _
    (Or.inr ⟨hlo,by rw [writeWord_sparse_size]; omega⟩)]
  exact writeWord_sparse_read_back _ _ _

theorem verifyBuffer_free (mem : ByteArray) (heap : Nat) (ws : List UInt256) :
    memLoad (UInt256.ofNat 64) (verifyBuffer mem heap ws) = UInt256.ofNat (allocateNext heap (32+32*ws.length)) := by
  apply mloadWordValue_of_readWithPadding
  · rw [verifyBuffer,writeWord_sparse_size]; change 64 < _; omega
  exact writeWord_sparse_read_back _ _ _

theorem verifyBuffer_prefix (mem : ByteArray) (heap : Nat) (ws : List UInt256) :
    MemoryPrefix mem (verifyBuffer mem heap ws) heap :=
  (writeWordSequence_prefix mem (heap+32) heap ws (by omega)).trans
    ((memoryPrefix_sparse_writeWord _ heap heap _ (Or.inl (le_refl _))).trans
      (memoryPrefix_sparse_writeWord _ 64 heap _ (Or.inr (by decide))))

theorem verifyBuffer_keccak (mem : ByteArray) (heap : UInt256) (ws : List UInt256)
    (hlo : 96 ≤ heap.toNat) (hb : heap.toNat+32 < UInt256.size) (hne : ws ≠ []) (hlen : ws.length ≤ 8) :
    keccakWord (heap+UInt256.ofNat 32) (memLoad heap (verifyBuffer mem heap.toNat ws))
      (verifyBuffer mem heap.toNat ws) = uInt256OfByteArray (KEC (wordBytes ws)) := by
  have hh : memLoad heap (verifyBuffer mem heap.toNat ws) = UInt256.ofNat (32*ws.length) :=
    mloadWordValue_of_readWithPadding (by rw [verifyBuffer,writeWord_sparse_size,writeWord_sparse_size]; omega)
      (verifyBuffer_header mem heap.toNat ws hlo)
  rw [hh,keccakWord,uadd_word_ofNat_toNat heap 32 hb,ulit_toNat' _ (by change 32*ws.length < 2^256; omega),
    verifyBuffer_payload mem heap.toNat ws hlo hne hlen]
  exact (uInt256OfByteArray_eq _).symm

end Benchmarks.EAS.EAS
