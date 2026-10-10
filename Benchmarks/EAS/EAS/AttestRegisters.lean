import Benchmarks.EAS.EAS.AttestInitialControl
import Benchmarks.EAS.EAS.AttestResultViews
import Benchmarks.EAS.EAS.AttestSchemaMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- The three reserved words are populated by the many-request entry point.
theorem attestEntryMemory_facts (kind : AttestCallKind) (mem : ByteArray) (data attester heap : UInt256)
    (hc : 224 ≤ mem.size) (hd : 224 ≤ data.toNat) (hdi : data.toNat+32 ≤ mem.size)
    (hf : memLoad (UInt256.ofNat 64) mem = heap) (hz : memLoad (UInt256.ofNat 96) mem = ⟨0⟩) :
    let m := attestEntryMemory kind mem data attester
    mem.size ≤ m.size ∧ memLoad (UInt256.ofNat 64) m = heap ∧ memLoad (UInt256.ofNat 96) m = ⟨0⟩ ∧
      memLoad data m = memLoad data mem ∧
      (kind = .many → memLoad (UInt256.ofNat 160) m = attester ∧ memLoad (UInt256.ofNat 192) m = data) := by
  cases kind with
  | single => exact ⟨le_refl _,hf,hz,rfl,by intro h; cases h⟩
  | many =>
    dsimp only [attestEntryMemory]
    have hc1 : 224 ≤ (Reasoning.Theory.writeWord mem 192 data).size := by rw [writeWord_sparse_size]; omega
    refine ⟨by simp only [writeWord_sparse_size]; omega,?_,?_,?_,?_⟩
    · rw [memLoad_write_below _ 160 (UInt256.ofNat 64) attester (by decide) (by change 96 ≤ _; omega),
        memLoad_write_below mem 192 (UInt256.ofNat 64) data (by decide) (by change 96 ≤ mem.size; omega),hf]
    · rw [memLoad_write_below _ 160 (UInt256.ofNat 96) attester (by decide) (by change 128 ≤ _; omega),
        memLoad_write_below mem 192 (UInt256.ofNat 96) data (by decide) (by change 128 ≤ mem.size; omega),hz]
    · rw [memLoad_write_above _ 160 data attester (by omega) (by rw [writeWord_sparse_size]; omega),
        memLoad_write_above mem 192 data data hd hdi]
    · intro _
      constructor
      · exact mloadWordValue_of_readWithPadding (by change 160 < _; rw [writeWord_sparse_size]; omega)
          (writeWord_sparse_read_back _ _ _)
      · rw [memLoad_write_above _ 160 (UInt256.ofNat 192) attester (by decide) hc1]
        exact mloadWordValue_of_readWithPadding (by change 192 < _; rw [writeWord_sparse_size]; omega)
          (writeWord_sparse_read_back _ _ _)

theorem attestResultRegisterMemory_facts (kind : AttestCallKind) (mem : ByteArray) (result heap data attester : UInt256)
    (hc : 224 ≤ mem.size) (hr : 160 ≤ result.toNat) (hri : result.toNat+32 ≤ mem.size)
    (hf : memLoad (UInt256.ofNat 64) mem = heap) (hz : memLoad (UInt256.ofNat 96) mem = ⟨0⟩)
    (hu : memLoad result mem = ⟨0⟩)
    (hg : kind = .many → memLoad (UInt256.ofNat 160) mem = attester ∧ memLoad (UInt256.ofNat 192) mem = data) :
    let m := attestResultRegisterMemory kind mem result
    mem.size ≤ m.size ∧ memLoad (UInt256.ofNat 64) m = heap ∧ memLoad (UInt256.ofNat 96) m = ⟨0⟩ ∧
      memLoad result m = ⟨0⟩ ∧
      (kind = .many → memLoad (UInt256.ofNat 128) m = result ∧
        memLoad (UInt256.ofNat 160) m = attester ∧ memLoad (UInt256.ofNat 192) m = data) := by
  cases kind with
  | single => exact ⟨le_refl _,hf,hz,hu,by intro h; cases h⟩
  | many =>
    dsimp only [attestResultRegisterMemory]
    refine ⟨by rw [writeWord_sparse_size]; omega,?_,?_,?_,?_⟩
    · exact (memLoad_write_below mem 128 (UInt256.ofNat 64) result (by decide) (by change 96 ≤ mem.size; omega)).trans hf
    · exact (memLoad_write_below mem 128 (UInt256.ofNat 96) result (by decide) (by change 128 ≤ mem.size; omega)).trans hz
    · exact (memLoad_write_above mem 128 result result hr hri).trans hu
    · intro _
      refine ⟨mloadWordValue_of_readWithPadding (by change 128 < _; rw [writeWord_sparse_size]; omega)
        (writeWord_sparse_read_back _ _ _),?_,?_⟩
      · exact (memLoad_write_above mem 128 (UInt256.ofNat 160) result (by decide) (by change 192 ≤ mem.size; omega)).trans (hg rfl).1
      · exact (memLoad_write_above mem 128 (UInt256.ofNat 192) result (by decide) hc).trans (hg rfl).2

end Benchmarks.EAS.EAS
