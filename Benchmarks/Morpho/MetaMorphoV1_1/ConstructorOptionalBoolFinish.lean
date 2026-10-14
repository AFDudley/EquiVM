import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_005
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_006

/-! The probing approval's final code-size check and success/fallback branch. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

theorem constructorOptionalBoolFinish {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw dummy spender token : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (flag : Bool)
    (hstack : R.length + 6 ≤ 1024)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1140⟩
      (dummy :: (if flag then ⟨1⟩ else ⟨0⟩) :: spender :: token :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (if flag && decide (extCodeSizeWord σ token ≠ ⟨0⟩) then ⟨1153⟩ else ⟨1420⟩)
      (spender :: token :: R) mem aw' out σ k' C' := by
  cases flag with
  | false =>
      have r1 := metaMorphoV1_1Creation_block_1140_fallthrough
        (by simp only [List.length_cons]; omega) rfl rd
      exact metaMorphoV1_1Creation_block_1147_taken_packed
        (by simp only [List.length_cons]; omega) (by decide) (by native_decide) r1
  | true =>
      have r1 := metaMorphoV1_1Creation_block_1140_taken
        (by simp only [List.length_cons]; omega) (by decide) (by native_decide) rd
      obtain ⟨_, _, _, r2⟩ := metaMorphoV1_1Creation_block_1489_packed
        (by omega) (by native_decide) r1
      simp only [metaMorphoV1_1Creation_block_1489_stack] at r2
      by_cases hz : extCodeSizeWord σ token = ⟨0⟩
      · obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1Creation_block_1147_taken_packed
          (by simp only [List.length_cons]; omega) (by rw [hz]; decide) (by native_decide) r2
        exact ⟨aw3, k3, C3, by simpa only [hz, ne_eq, not_true_eq_false, decide_false,
          Bool.true_and, Bool.false_eq_true, if_false] using r3⟩
      · obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1Creation_block_1147_fallthrough_packed
          (by simp only [List.length_cons]; omega)
          (by rw [isZero_eq_zero_of_ne hz]; decide) r2
        exact ⟨aw3, k3, C3, by simpa only [hz, ne_eq, not_false_eq_true, decide_true,
          Bool.true_and, if_true] using r3⟩

end Benchmarks.Morpho.MetaMorphoV1_1
