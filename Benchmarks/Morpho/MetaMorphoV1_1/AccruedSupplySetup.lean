import Benchmarks.Morpho.MetaMorphoV1_1.StructAllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.BoundedCallMemory
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_069

/-! Initial market-struct allocation and Morpho code guard in accrued supply balance. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def accruedSupplyInitialMem (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  wordSequenceMemory (writeWord mem 64 (nextCursor ptr ⟨192⟩)) ptr.toNat
    [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]

theorem accruedSupplyInitialMem_free (mem : ByteArray) (ptr : UInt256)
    (hlo : 96 ≤ ptr.toNat) :
    memLoad ⟨64⟩ (accruedSupplyInitialMem mem ptr) = nextCursor ptr ⟨192⟩ := by
  change memLoad (UInt256.ofNat 64) _ = _
  rw [accruedSupplyInitialMem, wordSequenceMemory_load_below _
    (by rw [writeWord_sparse_size]; omega) hlo (by decide)]
  exact loadedWord_of_read (by change 64 + 32 ≤ _; rw [writeWord_sparse_size]; omega)
    (writeWord_sparse_read_back _ _ _)

theorem accruedSupplyInitialMem_size (mem : ByteArray) (ptr : UInt256) :
    (accruedSupplyInitialMem mem ptr).size = max (max mem.size 96) (ptr.toNat + 192) := by
  rw [accruedSupplyInitialMem, wordSequenceMemory_size_nonempty _ _ _ (by simp),
    writeWord_sparse_size]
  rfl

theorem accruedSupplyInitialMem_prefix (mem : ByteArray) (ptr : UInt256) :
    MemoryPrefix mem (accruedSupplyInitialMem mem ptr) ptr.toNat :=
  (memoryPrefix_sparse_writeWord mem 64 ptr.toNat _ (.inr (by decide))).trans
    (wordSequenceMemory_prefix _ _ _)

theorem accruedSupplyZeroWrites (mem : ByteArray) (ptr : UInt256)
    (hfit : allocationFits ptr ⟨192⟩) :
    metaMorphoV1_1_block_14969_fallthrough_memory
      (mem := writeWord mem 64 (nextCursor ptr ⟨192⟩))
      (x0 := ptr) (x1 := ⟨160⟩) (x2 := ⟨0⟩) = accruedSupplyInitialMem mem ptr := by
  have hb : ptr.toNat + 192 < 2 ^ 64 :=
    (allocationFits_aligned ptr ⟨192⟩ (by decide +kernel)).mp hfit
  have hadd (n : Nat) (hn : n ≤ 192) : (ptr + UInt256.ofNat n).toNat = ptr.toNat + n :=
    uadd_word_ofNat_toNat ptr n (lt_trans (by omega : ptr.toNat + n < 2 ^ 64) (by decide))
  simp only [metaMorphoV1_1_block_14969_fallthrough_memory,
    hadd 32 (by decide), hadd 64 (by decide), hadd 96 (by decide),
    hadd 128 (by decide), show (ptr + (⟨160⟩ : UInt256)).toNat = ptr.toNat + 160 from
      hadd 160 (by decide), accruedSupplyInitialMem, wordSequenceMemory, Reasoning.Theory.writeWord,
    Nat.add_assoc]

set_option maxRecDepth 2000 in
theorem accruedSupplyInitial {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params id : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 12 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr)
    (rd : RD (deployedRuntime v) I g s0 ⟨14951⟩ (params :: id :: R) mem aw rdata σ k C) :
    (¬ allocationFits ptr ⟨192⟩ ∧ RDrev (deployedRuntime v) g s0) ∨
    (allocationFits ptr ⟨192⟩ ∧
      extCodeSizeWord σ (UInt256.ofNat v.MORPHO.toNat) = ⟨0⟩ ∧
      RDrev (deployedRuntime v) g s0) ∨
    (allocationFits ptr ⟨192⟩ ∧
      extCodeSizeWord σ (UInt256.ofNat v.MORPHO.toNat) ≠ ⟨0⟩ ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨15050⟩
        (params :: UInt256.ofNat v.MORPHO.toNat :: UInt256.ofNat v.MORPHO.toNat ::
          id :: ⟨0⟩ :: R) (accruedSupplyInitialMem mem ptr) aw' rdata σ k' C') := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_14951_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  simp only [metaMorphoV1_1_block_14951_stack, hf] at h1
  by_cases hfit : allocationFits ptr ⟨192⟩
  · obtain ⟨aw2, k2, C2, h2⟩ := allocateStruct192Return v
      (by simp only [List.length_cons]; omega) hfit
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
    have hm : UInt256.land (wordsOf (immStore v) "MORPHO")
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1)) = UInt256.ofNat v.MORPHO.toNat := by
      rw [wordsOf_immStore_MORPHO]
      exact solcAddrMask_clean (addressWord_val_canonical v.MORPHO)
    by_cases hz : extCodeSizeWord σ (UInt256.ofNat v.MORPHO.toNat) = ⟨0⟩
    · obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_14969_taken_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [hm, hz]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
      exact .inr (.inl ⟨hfit, hz, metaMorphoV1_1_block_917
        (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_14969_taken_stack, List.length_cons]; omega) h3⟩)
    · obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_14969_fallthrough_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by rw [hm]; exact isZero_eq_zero_of_ne hz) h2
      have hw := accruedSupplyZeroWrites mem ptr hfit
      change metaMorphoV1_1_block_14969_fallthrough_memory
        (mem := writeWord mem 64 (nextCursor ptr ⟨192⟩))
        (x0 := ptr) (x1 := UInt256.ofNat 160) (x2 := ⟨0⟩) = _ at hw
      rw [hw] at h3
      simp only [metaMorphoV1_1_block_14969_fallthrough_stack, hm] at h3
      rw [wordsOf_immStore_MORPHO] at h3
      exact .inr (.inr ⟨hfit, hz, aw3, k3, C3, h3⟩)
  · exact .inl ⟨hfit, allocateStruct192Revert v
      (by simp only [List.length_cons]; omega) hfit h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
