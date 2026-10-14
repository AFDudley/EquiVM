import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_018

/-! Creation-code counterpart of the Address call-result verification routines. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

theorem constructorAddressVerifyReturn {tail : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {target ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (hvalid : memLoad ptr mem ≠ ⟨0⟩ ∨ extCodeSizeWord σ target ≠ ⟨0⟩)
    (hret : (D_J metaMorphoV1_1CreationBytecode 0).contains ret = true)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨3799⟩
      (target :: ⟨1⟩ :: ptr :: ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ret (ptr :: R) mem aw' out σ k' C' := by
  have h1 := metaMorphoV1_1Creation_block_3799_taken
    (by simp only [List.length_cons]; omega) (by decide)
    (by native_decide) rd
  have hfinish {aw k C} (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨3844⟩
      (⟨0⟩ :: target :: ptr :: ret :: R) mem aw out σ k C) :
      ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ret (ptr :: R) mem aw' out σ k' C' := by
    have h2 := metaMorphoV1_1Creation_block_3844_fallthrough
      (by simp only [List.length_cons]; omega) rfl rd
    exact metaMorphoV1_1Creation_block_3849_packed
      (by omega) hret h2
  by_cases hz : memLoad ptr mem = ⟨0⟩
  · have hc := hvalid.resolve_left (not_not_intro hz)
    have h2 := metaMorphoV1_1Creation_block_3835_taken
      (by simp only [List.length_cons]; omega)
      (by rw [hz]; decide) (by native_decide) h1
    obtain ⟨_, _, h3⟩ := metaMorphoV1_1Creation_block_3884
      (by simp only [List.length_cons]; omega)
      (by native_decide) h2
    apply hfinish
    simpa only [metaMorphoV1_1Creation_block_3884_stack, isZero_eq_zero_of_ne hc] using h3
  · have h2 := metaMorphoV1_1Creation_block_3835_fallthrough
      (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hz) h1
    apply hfinish
    simpa only [metaMorphoV1_1Creation_block_3835_fallthrough_stack, isZero_eq_zero_of_ne hz] using h2

theorem constructorAddressVerifyRevertCall {tail : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {target ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 7 ≤ 1024)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨3799⟩
      (target :: ⟨0⟩ :: ptr :: ret :: R) mem aw out σ k C) :
    RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0 := by
  have h1 := metaMorphoV1_1Creation_block_3799_fallthrough
    (by simp only [List.length_cons]; omega) rfl rd
  by_cases hz : memLoad ptr mem = ⟨0⟩
  · have h2 := metaMorphoV1_1Creation_block_3805_taken
      (by simp only [List.length_cons]; omega) (by rw [hz]; decide)
      (by native_decide) h1
    exact metaMorphoV1_1Creation_block_3820
      (by simp only [metaMorphoV1_1Creation_block_3805_taken_stack, List.length_cons]; omega) h2
  · have h2 := metaMorphoV1_1Creation_block_3805_fallthrough
      (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hz) h1
    exact metaMorphoV1_1Creation_block_3813
      (by simp only [List.length_cons]; omega) h2

theorem constructorAddressVerifyRevertCode {tail : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {target ptr ret : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024)
    (hlen : memLoad ptr mem = ⟨0⟩) (hcode : extCodeSizeWord σ target = ⟨0⟩)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨3799⟩
      (target :: ⟨1⟩ :: ptr :: ret :: R) mem aw out σ k C) :
    RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0 := by
  have h1 := metaMorphoV1_1Creation_block_3799_taken
    (by simp only [List.length_cons]; omega) (by decide)
    (by native_decide) rd
  have h2 := metaMorphoV1_1Creation_block_3835_taken
    (by simp only [List.length_cons]; omega) (by rw [hlen]; decide)
    (by native_decide) h1
  obtain ⟨_, _, h3⟩ := metaMorphoV1_1Creation_block_3884
    (by simp only [List.length_cons]; omega)
    (by native_decide) h2
  have h4 := metaMorphoV1_1Creation_block_3844_taken
    (by simp only [List.length_cons]; omega) (by rw [hcode]; decide)
    (by native_decide) h3
  exact metaMorphoV1_1Creation_block_3852
    (by simp only [metaMorphoV1_1Creation_block_3844_taken_stack, List.length_cons]; omega) h4

end Benchmarks.Morpho.MetaMorphoV1_1
