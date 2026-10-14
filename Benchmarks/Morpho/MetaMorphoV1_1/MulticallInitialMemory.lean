import Benchmarks.Morpho.MetaMorphoV1_1.MulticallMemory
import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayInitMemory

/-! The allocated result array initially points every element to the shared empty byte buffer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.Attester

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def multicallInitialMemory (mem : ByteArray) (n : Nat) : ByteArray :=
  wordArrayMemory mem 128 n (fun _ ↦ ⟨96⟩)

theorem multicallInitialMemory_zero (mem : ByteArray) (n : Nat) (hmem : mem.size ≤ 96) :
    memLoad ⟨96⟩ (multicallInitialMemory mem n) = ⟨0⟩ := by
  change memLoad (UInt256.ofNat 96) (wordArrayMemory mem 128 n _) = _
  rw [wordArrayMemory, wordSequenceMemory_load_below _
    (by rw [wordArrayHeaderMemory_size _ _ _ (by decide)]; omega) (by decide) (by decide)]
  apply loadedWord_of_read
  · rw [wordArrayHeaderMemory_size _ _ _ (by decide)]; change 128 ≤ _; omega
  · change (writeWord (writeWord mem 64 _) 128 _).readWithPadding 96 32 = _
    exact writeWord_read_zero_gap _ 128 96 _ (by rw [writeWord_sparse_size]; omega) (by decide)

theorem multicallInitialMemory_ready (mem : ByteArray) (n : Nat)
    (hmem : mem.size ≤ 96) (hf : 160 + 32 * n < 2 ^ 64) :
    MulticallMemory (multicallInitialMemory mem n) (UInt256.ofNat (160 + 32 * n))
      (List.replicate n ByteArray.empty) := by
  have hn : 160 + 32 * n < UInt256.size := lt_trans hf (by decide)
  have hs : (multicallInitialMemory mem n).size = 160 + 32 * n := by
    rw [multicallInitialMemory, wordArrayMemory_size _ _ _ _ (by decide)]
    omega
  have hz := multicallInitialMemory_zero mem n hmem
  refine ⟨by rwa [UInt256.toNat_ofNat_of_lt hn], ?_, ?_, ?_, hz, ?_, ?_⟩
  · rw [List.length_replicate, UInt256.toNat_ofNat_of_lt hn]
  · rw [List.length_replicate, hs]
  · have he := wordArrayMemory_freePtr mem 128 n (fun _ ↦ (⟨96⟩ : UInt256)) (by decide)
    simpa only [show 128 + 32 * (n + 1) = 160 + 32 * n by omega] using he
  · simpa only [List.length_replicate] using
      wordArrayMemory_length mem 128 n (fun _ ↦ (⟨96⟩ : UInt256)) (by decide) (by decide)
  · intro j hj
    simp only [List.length_replicate] at hj
    simp only [List.getElem_replicate]
    refine ⟨⟨96⟩, .inl rfl, ?_, by decide, ?_, ?_⟩
    · rw [UInt256.toNat_ofNat_of_lt hn]
      change 96 + 32 + 0 ≤ _
      omega
    · exact ⟨by rw [hs]; change 128 ≤ _; omega, hz, byteArray_readWithPadding_zero _ _⟩
    · exact wordArrayMemory_data mem 128 n (fun _ ↦ (⟨96⟩ : UInt256)) hj (by omega)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
