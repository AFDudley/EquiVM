import Benchmarks.EAS.EAS.RecordMemory
import Benchmarks.EAS.EAS.RecordArrayViews
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- GENERALIZES memLoad_write_below to an initialized load above a word write.
theorem memLoad_write_above (mem : ByteArray) (off : Nat) (ptr word : UInt256)
    (habove : off+32 ≤ ptr.toNat) (hin : ptr.toNat+32 ≤ mem.size) :
    memLoad ptr (Reasoning.Theory.writeWord mem off word) = memLoad ptr mem := by
  change (if ptr.toNat ≥ (Reasoning.Theory.writeWord mem off word).size then (⟨0⟩ : UInt256)
    else UInt256.ofNat (fromByteArrayBigEndian ((Reasoning.Theory.writeWord mem off word).readWithPadding ptr.toNat 32))) =
    (if ptr.toNat ≥ mem.size then (⟨0⟩ : UInt256)
    else UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding ptr.toNat 32)))
  rw [if_neg (by rw [writeWord_sparse_size]; omega),if_neg (by omega),
    writeWord_sparse_read_preserved _ _ _ _ (Or.inr ⟨habove,hin⟩)]

theorem AttestationMemoryView.setUID {mem : ByteArray} {src dataPtr : UInt256} {a : AttestationRecord}
    (h : AttestationMemoryView mem src dataPtr a) (word : UInt256)
    (hdata : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ src.toNat) (hb : src.toNat+320 < UInt256.size) :
    AttestationMemoryView (Reasoning.Theory.writeWord mem src.toNat word) src dataPtr {a with uid := word} := by
  have hs (n : Nat) (hn : n ≤ 320) : (src+UInt256.ofNat n).toNat = src.toNat+n :=
    uadd_word_ofNat_toNat src n (by omega)
  have hi := h.sourceCovered
  have hload (n : Nat) (hlo : 32 ≤ n) (hhi : n ≤ 288) :
      memLoad (src+UInt256.ofNat n) (Reasoning.Theory.writeWord mem src.toNat word) =
        memLoad (src+UInt256.ofNat n) mem :=
    memLoad_write_above _ _ _ _ (by rw [hs n (by omega)]; omega) (by rw [hs n (by omega)]; omega)
  have hself : memLoad src (Reasoning.Theory.writeWord mem src.toNat word) = word :=
    mloadWordValue_of_readWithPadding (by rw [writeWord_sparse_size]; omega) (writeWord_sparse_read_back _ _ _)
  have hp := memoryPrefix_sparse_writeWord mem src.toNat src.toNat word (Or.inl (le_refl _))
  refine ⟨h.sourceLow,h.dataLow,?_,?_,(hload 288 (by decide) (by decide)).trans h.pointer,?_,?_,?_⟩
  · rw [writeWord_sparse_size]; omega
  · rw [writeWord_sparse_size]; exact le_trans h.dataCovered (Nat.le_max_left _ _)
  · exact (memLoad_write_below _ _ _ _ (by omega) (by have hh := h.dataCovered; omega)).trans h.length
  · have hf := h.fields
    simp only [attestationEncodeHeadWords,attestationEncodeFirstWords,attestationEncodeLastWords,
      AttestationRecord.words,List.cons_append,List.nil_append,List.cons.injEq,and_true] at hf ⊢
    simp only [hself,hload 32 (by decide) (by decide),hload 64 (by decide) (by decide),
      hload 96 (by decide) (by decide),hload 128 (by decide) (by decide),hload 160 (by decide) (by decide),
      hload 192 (by decide) (by decide),hload 224 (by decide) (by decide),hload 256 (by decide) (by decide)]
    exact ⟨True.intro,hf.2⟩
  · exact (memoryPrefix_read_prefix hp (dataPtr.toNat+32) ((a.data.size+31)/32) a.data.size
      (by have hh := h.dataLow; omega) hdata h.dataCovered (by omega) (by omega)).trans h.payload

end Benchmarks.EAS.EAS
