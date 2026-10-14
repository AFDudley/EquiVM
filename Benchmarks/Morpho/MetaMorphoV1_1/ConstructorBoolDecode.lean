import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_006
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_017
import Reasoning.ABIComposite

/-! The creation code's shared strict ABI Boolean decoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

theorem constructorBoolDecode {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw start stop ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hout : out.size < 2 ^ 255)
    (hlen : UInt256.sub stop start = UInt256.ofNat out.size)
    (hword : 32 ≤ out.size → memLoad start mem = calldataWord out 0)
    (hret : (D_J metaMorphoV1_1CreationBytecode 0).contains ret = true)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨3668⟩
      (start :: stop :: ret :: R) mem aw out σ k C) :
    (¬ BoolReturnValid out ∧ RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    (BoolReturnValid out ∧ ∃ aw' k' C',
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ret
        (calldataWord out 0 :: R) mem aw' out σ k' C') := by
  by_cases hl : 32 ≤ out.size
  · have r1 := metaMorphoV1_1Creation_block_3668_fallthrough
      (by simp only [List.length_cons]; omega)
      (by rw [hlen]; exact slt_ofNat_lit_zero (by decide) hl hout) rd
    by_cases hb : calldataWord out 0 = ⟨0⟩ ∨ calldataWord out 0 = ⟨1⟩
    · have hc : UInt256.sub (memLoad start mem)
          (UInt256.isZero (UInt256.isZero (memLoad start mem))) = ⟨0⟩ := by
        rw [hword hl]
        rcases hb with hz | ho
        · rw [hz]; decide
        · rw [ho]; decide
      have r2 := metaMorphoV1_1Creation_block_3680_fallthrough
        (by simp only [List.length_cons]; omega) hc r1
      obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1Creation_block_3690_packed
        (by omega) hret r2
      exact .inr ⟨⟨hl, hb⟩, aw3, k3, C3, by
        simpa only [metaMorphoV1_1Creation_block_3690_stack,
          metaMorphoV1_1Creation_block_3680_fallthrough_stack, hword hl] using r3⟩
    · have hz : calldataWord out 0 ≠ ⟨0⟩ := fun h => hb (.inl h)
      have ho : calldataWord out 0 ≠ ⟨1⟩ := fun h => hb (.inr h)
      have hc : UInt256.sub (memLoad start mem)
          (UInt256.isZero (UInt256.isZero (memLoad start mem))) ≠ ⟨0⟩ := by
        rw [hword hl, isZero_eq_zero_of_ne hz]
        exact u256_sub_ne_zero_of_ne ho
      have r2 := metaMorphoV1_1Creation_block_3680_taken
        (by simp only [List.length_cons]; omega) hc (by native_decide) r1
      exact .inl ⟨fun h => hb h.2, metaMorphoV1_1Creation_block_1596
        (by simp only [metaMorphoV1_1Creation_block_3680_taken_stack, List.length_cons]; omega) r2⟩
  · have hc : UInt256.slt (UInt256.ofNat out.size) (UInt256.ofNat 32) = ⟨1⟩ :=
      slt_ofNat_lit_one_low (n := out.size) (m := 32) (by decide) (by omega)
    have r1 := metaMorphoV1_1Creation_block_3668_taken
      (by simp only [List.length_cons]; omega)
      (by rw [hlen, hc]; decide) (by native_decide) rd
    exact .inl ⟨fun h => hl h.1, metaMorphoV1_1Creation_block_1596
      (by simp only [metaMorphoV1_1Creation_block_3668_taken_stack, List.length_cons]; omega) r1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
