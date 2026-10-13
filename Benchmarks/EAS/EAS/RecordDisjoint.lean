import Benchmarks.EAS.EAS.RecordUID
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem AttestationMemoryView.write_disjoint {mem : ByteArray} {src dataPtr : UInt256}
    {a : AttestationRecord} (h : AttestationMemoryView mem src dataPtr a)
    (dst : Nat) (word : UInt256) (hb : src.toNat+320 < UInt256.size)
    (hs : src.toNat+320 ≤ dst ∨ dst+32 ≤ src.toNat)
    (hd : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ dst ∨ dst+32 ≤ dataPtr.toNat) :
    AttestationMemoryView (Reasoning.Theory.writeWord mem dst word) src dataPtr a := by
  have hc := h.sourceCovered
  have hdc := h.dataCovered
  have hload (ptr : UInt256) (hlo : src.toNat ≤ ptr.toNat) (hhi : ptr.toNat+32 ≤ src.toNat+320) :
      memLoad ptr (Reasoning.Theory.writeWord mem dst word) = memLoad ptr mem := by
    rcases hs with hs | hs
    · exact memLoad_write_below _ _ _ _ (by omega) (by omega)
    · exact memLoad_write_above _ _ _ _ (by omega) (by omega)
  have hoff (n : Nat) (hn : n ≤ 288) :
      memLoad (src+UInt256.ofNat n) (Reasoning.Theory.writeWord mem dst word) =
        memLoad (src+UInt256.ofNat n) mem := by
    have he : (src+UInt256.ofNat n).toNat = src.toNat+n := uadd_word_ofNat_toNat _ _ (by omega)
    exact hload _ (by rw [he]; omega) (by rw [he]; omega)
  refine ⟨h.sourceLow,h.dataLow,?_,?_,(hoff 288 (by decide)).trans h.pointer,?_,?_,?_⟩
  · rw [writeWord_sparse_size]; omega
  · rw [writeWord_sparse_size]; omega
  · rcases hd with hd | hd
    · exact (memLoad_write_below _ _ _ _ (by omega) (by omega)).trans h.length
    · exact (memLoad_write_above _ _ _ _ hd (by omega)).trans h.length
  · rw [← h.fields]
    simp only [attestationEncodeHeadWords,attestationEncodeFirstWords,attestationEncodeLastWords,
      hload src (le_refl _) (by omega),hoff 32 (by decide),hoff 64 (by decide),hoff 96 (by decide),
      hoff 128 (by decide),hoff 160 (by decide),hoff 192 (by decide),hoff 224 (by decide),hoff 256 (by decide)]
  · rcases hd with hd | hd
    · exact (writeWord_read_below_len _ _ _ _ _ (by omega) (by omega)).trans h.payload
    · exact (writeWord_read_above_len _ _ _ _ _ (by omega) (by omega)).trans h.payload

end Benchmarks.EAS.EAS
