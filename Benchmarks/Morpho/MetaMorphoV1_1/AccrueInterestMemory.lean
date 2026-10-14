import Benchmarks.Morpho.MetaMorphoV1_1.AccrueInterestRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.MappingScratchMemory
import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayInitMemory

/-! Heap and free-cursor preservation by interest-accrual events and ERC20 minting. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

-- LIBRARY CANDIDATE: a scratch word at the free cursor preserves that cursor.
theorem writeFreeWord_free {mem : ByteArray} {ptr : UInt256} (word : UInt256)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hmem : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) :
    memLoad ⟨64⟩ (writeWord mem ptr.toNat word) = ptr := by
  rw [Reasoning.Theory.writeWord,
    memLoad_write_disjoint mem ptr.toNat ⟨64⟩ word hmem (.inl hlo)]
  exact hfree

theorem accrueInterestStoreMemory_free {mem : ByteArray} {ptr : UInt256}
    (lost total : UInt256) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hmem : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) :
    memLoad ⟨64⟩ (accrueInterestStoreMemory mem lost total) = ptr := by
  have hf := writeFreeWord_free total hfree hmem hlo
  simp only [accrueInterestStoreMemory, hfree, hf]
  exact writeFreeWord_free lost hf (by rw [writeWord_sparse_size]; omega) hlo

theorem accrueInterestStoreMemory_prefix {mem : ByteArray} {ptr : UInt256}
    (lost total : UInt256) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hmem : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) :
    MemoryPrefix mem (accrueInterestStoreMemory mem lost total) ptr.toNat := by
  have hf := writeFreeWord_free total hfree hmem hlo
  simp only [accrueInterestStoreMemory, hfree, hf]
  exact (memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _))).trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _)))

theorem accrueInterestStoreMemory_size {mem : ByteArray} {ptr : UInt256}
    (lost total : UInt256) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hmem : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) :
    (accrueInterestStoreMemory mem lost total).size = max mem.size (ptr.toNat + 32) := by
  have hf := writeFreeWord_free total hfree hmem hlo
  simp only [accrueInterestStoreMemory, hfree, hf, writeWord_sparse_size, max_self, max_assoc]

theorem accrueInterestStoreMemory_zero {mem : ByteArray} {ptr : UInt256}
    (lost total : UInt256) (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 128 ≤ ptr.toNat)
    (hm : mem.size = 96 ∨ 128 ≤ mem.size) (hz : memLoad ⟨96⟩ mem = ⟨0⟩) :
    memLoad ⟨96⟩ (accrueInterestStoreMemory mem lost total) = ⟨0⟩ := by
  rcases hm with hm | hm
  · have hf := writeFreeWord_free total hfree (by omega) (by omega)
    have hz1 : memLoad ⟨96⟩ (writeWord mem ptr.toNat total) = ⟨0⟩ := by
      apply mloadWordValue_of_readWithPadding
        (by change 96 < _; rw [writeWord_sparse_size]; omega)
      exact writeWord_read_zero_gap mem ptr.toNat 96 total (by omega) hlo
    simp only [accrueInterestStoreMemory, hfree, hf]
    exact ((memoryPrefix_sparse_writeWord _ ptr.toNat ptr.toNat lost (.inl (le_refl _))).load_preserved
      (off := 96) (by decide) hlo (by rw [writeWord_sparse_size]; omega) (by decide)).trans hz1
  · exact ((accrueInterestStoreMemory_prefix lost total hfree (by omega) (by omega)).load_preserved
      (off := 96) (by decide) hlo hm (by decide)).trans hz

theorem mintReturnMemory_free {mem : ByteArray} {ptr : UInt256}
    (recipient : AccountAddress) (value : UInt256) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hmem : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) :
    memLoad ⟨64⟩ (mintReturnMemory mem recipient value) = ptr := by
  have hf := (twoWordHashMem_free (UInt256.ofNat recipient.toNat) ⟨0⟩ hmem).trans hfree
  simp only [mintReturnMemory, hf]
  exact writeFreeWord_free value hf
    (le_trans hmem (twoWordHashMem_prefix mem _ _ ptr.toNat).size) hlo

theorem mintReturnMemory_prefix {mem : ByteArray} {ptr : UInt256}
    (recipient : AccountAddress) (value : UInt256) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hmem : 96 ≤ mem.size) : MemoryPrefix mem (mintReturnMemory mem recipient value) ptr.toNat := by
  have hf := (twoWordHashMem_free (UInt256.ofNat recipient.toNat) ⟨0⟩ hmem).trans hfree
  simp only [mintReturnMemory, hf]
  exact (twoWordHashMem_prefix mem _ _ ptr.toNat).trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _)))

theorem accrueInterestFinishMemory_free {mem : ByteArray} {ptr : UInt256}
    (total shares : UInt256) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hmem : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hptr : ptr.toNat < 2 ^ 64) :
    memLoad ⟨64⟩ (accrueInterestFinishMemory mem total shares) = ptr := by
  have hp := uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)
  simp only [accrueInterestFinishMemory, hfree, hp]
  change memLoad ⟨64⟩ (shares.toByteArray.write 0 (writeWord mem ptr.toNat total)
    (ptr.toNat + 32) 32) = ptr
  rw [memLoad_write_disjoint _ (ptr.toNat + 32) ⟨64⟩ shares
    (by change 96 ≤ _; rw [writeWord_sparse_size]; omega)
    (.inl (by change 96 ≤ ptr.toNat + 32; omega))]
  exact writeFreeWord_free total hfree hmem hlo

theorem accrueInterestFinishMemory_prefix {mem : ByteArray} {ptr : UInt256}
    (total shares : UInt256) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hptr : ptr.toNat < 2 ^ 64) :
    MemoryPrefix mem (accrueInterestFinishMemory mem total shares) ptr.toNat := by
  have hp := uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)
  simp only [accrueInterestFinishMemory, hfree, hp]
  exact (memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _))).trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (.inl (by omega)))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
