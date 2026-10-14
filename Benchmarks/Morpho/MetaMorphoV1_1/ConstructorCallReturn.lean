import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.CallReturnAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_012
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_016

/-! The creation code's shared raw-return buffer allocator and copier. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem constructorCallReturnBuffer {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024) (hptr : ptr.toNat < 2 ^ 64)
    (hout : out.size < UInt256.size) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hret : (D_J metaMorphoV1_1CreationBytecode 0).contains ret = true)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨3498⟩
      (ret :: R) mem aw out σ k C) :
    (¬ callReturnFits ptr out ∧ RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    (callReturnFits ptr out ∧ ∃ aw' k' C',
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ret (callReturnPointer ptr out :: R)
        (callReturnMemory mem ptr out) aw' out σ k' C') := by
  change memLoad (UInt256.ofNat 64) mem = ptr at hfree
  have ho : (UInt256.ofNat out.size).toNat = out.size := UInt256.toNat_ofNat_of_lt hout
  by_cases hz : out.size = 0
  · have r1 := metaMorphoV1_1Creation_block_3498_taken
      (by simp only [List.length_cons]; omega) (by rw [hz]; decide) (by native_decide) rd
    obtain ⟨aw2, k2, C2, r2⟩ := metaMorphoV1_1Creation_block_3540_packed (by omega) hret r1
    exact .inr ⟨.inl hz, aw2, k2, C2, by
      simpa only [callReturnPointer, callReturnMemory, hz, if_pos rfl,
        metaMorphoV1_1Creation_block_3540_stack] using r2⟩
  · have hn : UInt256.ofNat out.size ≠ ⟨0⟩ := by
      intro he
      have hh := congrArg UInt256.toNat he
      rw [ho] at hh
      exact hz hh
    have r1 := metaMorphoV1_1Creation_block_3498_fallthrough
      (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hn) rd
    have r2 := metaMorphoV1_1Creation_block_3505 (by omega) (by native_decide) r1
    by_cases hsmall : out.size < 2 ^ 64
    · have r3 := metaMorphoV1_1Creation_block_2663_fallthrough
        (by simp only [List.length_cons]; omega)
        (ugt_zero (by rw [ho]; change out.size ≤ 2 ^ 64 - 1; omega)) r2
      have r4 := metaMorphoV1_1Creation_block_2678
        (by simp only [List.length_cons]; omega) (by native_decide) r3
      simp only [metaMorphoV1_1Creation_block_2678_stack, callReturnSizeWord out.size hsmall] at r4
      have r5 := metaMorphoV1_1Creation_block_3515 (by omega) (by native_decide) r4
      simp only [metaMorphoV1_1Creation_block_3515_stack, hfree] at r5
      by_cases hf : allocationFits ptr (UInt256.ofNat (32 + out.size))
      · obtain ⟨_, _, _, r6⟩ := constructorAllocateReturn
          (by simp only [List.length_cons]; omega)
          ((allocationFits_bytesAlloc ptr out.size hsmall).mpr hf) (by native_decide) r5
        rw [nextCursor_bytesAllocSize ptr out.size hsmall] at r6
        obtain ⟨aw7, k7, C7, r7⟩ := metaMorphoV1_1Creation_block_3529_packed (by omega)
          (by change 0 + (UInt256.ofNat out.size).toNat ≤ out.size; omega) hret r6
        have hp : (ptr + UInt256.ofNat 32).toNat = ptr.toNat + 32 :=
          uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)
        exact .inr ⟨.inr ⟨hsmall, hf⟩, aw7, k7, C7, by
          simpa only [callReturnPointer, callReturnMemory, if_neg hz,
            metaMorphoV1_1Creation_block_3529_stack, metaMorphoV1_1Creation_block_3529_memory,
            hp, ho, show (⟨0⟩ : UInt256).toNat = 0 from rfl, bytesAllocMem,
            Reasoning.Theory.writeWord] using r7⟩
      · exact .inl ⟨fun h => hf ((h.resolve_left hz).2),
          constructorAllocateRevert (by simp only [List.length_cons]; omega)
            (fun h => hf ((allocationFits_bytesAlloc ptr out.size hsmall).mp h)) r5⟩
    · have r3 := metaMorphoV1_1Creation_block_2663_taken
        (by simp only [List.length_cons]; omega)
        (by rw [ugt_one (by rw [ho]; change 2 ^ 64 - 1 < out.size; omega)]; decide)
        (by native_decide) r2
      exact .inl ⟨fun h => hsmall ((h.resolve_left hz).1),
        metaMorphoV1_1Creation_block_1854 (by simp only [List.length_cons]; omega) r3⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
