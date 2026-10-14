import Benchmarks.Morpho.MetaMorphoV1_1.StructAllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.StructReturnMemory
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_031
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_032

/-! The two reservations before a calldata allocation row is materialized. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem reallocateRowAllocationFits (ptr : UInt256) :
    allocationFits ptr ⟨224⟩ ↔
      allocationFits ptr ⟨64⟩ ∧ allocationFits (nextCursor ptr ⟨64⟩) ⟨160⟩ :=
  allocationFits_aligned_split ptr 64 160 (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem reallocateRowNextCursor (ptr : UInt256) :
    nextCursor (nextCursor ptr ⟨64⟩) ⟨160⟩ = nextCursor ptr ⟨224⟩ := by
  change (ptr + (⟨64⟩ : UInt256)) + (⟨160⟩ : UInt256) = ptr + (⟨224⟩ : UInt256)
  rw [u256_add_assoc]
  rfl

def reallocateRowReservedMem (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  writeWord (writeWord mem 64 (nextCursor ptr ⟨64⟩)) 64 (nextCursor ptr ⟨224⟩)

set_option maxRecDepth 2000 in
theorem reallocateRowAllocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr remaining withdrawn base : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr)
    (hlo : 160 ≤ remaining.toNat) (hhi : remaining.toNat < 2 ^ 255)
    (rd : RD (deployedRuntime v) I g s0 ⟨5985⟩ (remaining :: withdrawn :: base :: R)
      mem aw rdata σ k C) :
    (¬ allocationFits ptr ⟨224⟩ ∧ RDrev (deployedRuntime v) g s0) ∨
    (allocationFits ptr ⟨224⟩ ∧ ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨6036⟩
      (nextCursor ptr ⟨64⟩ :: ⟨160⟩ :: ptr :: withdrawn :: base :: R)
      (reallocateRowReservedMem mem ptr) aw' rdata σ k' C') := by
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  by_cases hfirst : allocationFits ptr ⟨64⟩
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_5985_fallthrough_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [hf]; exact (allocationGuard_eq_zero_iff ptr ⟨64⟩).mpr hfirst) rd
    simp only [metaMorphoV1_1_block_5985_fallthrough_stack, hf] at h1
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_6012_fallthrough_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (slt_lit_zero (by decide) hlo hhi) h1
    change RD (deployedRuntime v) I g s0 ⟨6023⟩ (ptr :: withdrawn :: base :: R)
      (writeWord mem 64 (nextCursor ptr ⟨64⟩)) aw2 rdata σ k2 C2 at h2
    obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_6023_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    have hnext : memLoad (UInt256.ofNat 64) (writeWord mem 64 (nextCursor ptr ⟨64⟩)) =
        nextCursor ptr ⟨64⟩ := memLoad_write_same _ _ _ _ rfl
    simp only [metaMorphoV1_1_block_6023_stack, hnext] at h3
    by_cases hsecond : allocationFits (nextCursor ptr ⟨64⟩) ⟨160⟩
    · obtain ⟨aw4, k4, C4, h4⟩ := allocateStruct160Return v
        (by simp only [List.length_cons]; omega) hsecond
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h3
      rw [reallocateRowNextCursor] at h4
      exact .inr ⟨(reallocateRowAllocationFits ptr).mpr ⟨hfirst, hsecond⟩, aw4, k4, C4, h4⟩
    · exact .inl ⟨fun h ↦ hsecond ((reallocateRowAllocationFits ptr).mp h).2,
        allocateStruct160Revert v (by simp only [List.length_cons]; omega) hsecond h3⟩
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_5985_taken_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [hf]; exact fun h ↦ hfirst ((allocationGuard_eq_zero_iff ptr ⟨64⟩).mp h))
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact .inl ⟨fun h ↦ hfirst ((reallocateRowAllocationFits ptr).mp h).1,
      metaMorphoV1_1_block_2690 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_5985_taken_stack, List.length_cons]; omega) h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
