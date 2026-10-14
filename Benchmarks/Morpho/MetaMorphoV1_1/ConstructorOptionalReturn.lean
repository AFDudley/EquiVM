import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorBoolDecode
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_018
import Benchmarks.Morpho.MetaMorphoV1_1.OptionalReturnSource

/-! Creation-code optional-return checks used by both fallback approval calls. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

theorem constructorOptionalReturnFinish {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw x y token ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024)
    (hret : (D_J metaMorphoV1_1CreationBytecode 0).contains ret = true)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨3745⟩
      (x :: y :: ⟨0⟩ :: token :: ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ret R
      mem aw' out σ k' C' := by
  have r1 := metaMorphoV1_1Creation_block_3745_fallthrough
    (by simp only [List.length_cons]; omega) rfl rd
  exact metaMorphoV1_1Creation_block_3752_packed (by omega) hret r1

theorem constructorOptionalReturn {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr token ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024) (hout : out.size < 2 ^ 64)
    (hlen : memLoad ptr mem = UInt256.ofNat out.size)
    (hword : 32 ≤ out.size → memLoad (ptr + UInt256.ofNat 32) mem = calldataWord out 0)
    (hret : (D_J metaMorphoV1_1CreationBytecode 0).contains ret = true)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨3732⟩
      (ptr :: token :: ret :: R) mem aw out σ k C) :
    (¬ optionalReturnValid out ∧ RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    (optionalReturnValid out ∧ ∃ aw' k' C',
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ret R mem aw' out σ k' C') := by
  by_cases hz : out.size = 0
  · have r1 := metaMorphoV1_1Creation_block_3732_fallthrough
      (by simp only [List.length_cons]; omega) (by rw [hlen, hz]; decide) rd
    refine .inr ⟨.inl hz, ?_⟩
    apply constructorOptionalReturnFinish (by omega) hret
    simpa only [metaMorphoV1_1Creation_block_3732_fallthrough_stack, hlen, hz,
      show UInt256.isZero (UInt256.isZero (UInt256.ofNat 0)) = (⟨0⟩ : UInt256) by decide] using r1
  · have hn : UInt256.ofNat out.size ≠ ⟨0⟩ := by
      intro he
      have hh := congrArg UInt256.toNat he
      rw [UInt256.toNat_ofNat_of_lt (by change _ < 2 ^ 256; omega)] at hh
      exact hz hh
    have r1 := metaMorphoV1_1Creation_block_3732_taken
      (by simp only [List.length_cons]; omega)
      (by rw [hlen, isZero_eq_zero_of_ne hn]; decide) (by native_decide) rd
    have r2 := metaMorphoV1_1Creation_block_3772
      (by simp only [List.length_cons]; omega) (by native_decide) r1
    simp only [metaMorphoV1_1Creation_block_3772_stack, hlen] at r2
    have hs : UInt256.sub ((ptr + UInt256.ofNat out.size) + UInt256.ofNat 32)
        (ptr + UInt256.ofNat 32) = UInt256.ofNat out.size := by
      rw [uadd_assoc, u256_add_comm (UInt256.ofNat out.size) (UInt256.ofNat 32),
        ← uadd_assoc, word_add_sub_left]
    rcases constructorBoolDecode (by simp only [List.length_cons]; omega)
        (by omega) hs hword (by native_decide) r2 with hbad | hgood
    · exact .inl ⟨fun h => hbad.1 ⟨(h.resolve_left hz).1, .inr (h.resolve_left hz).2⟩, hbad.2⟩
    · obtain ⟨hb, _, _, _, r3⟩ := hgood
      have r4 := metaMorphoV1_1Creation_block_3791
        (by simp only [List.length_cons]; omega) (by native_decide) r3
      by_cases ho : calldataWord out 0 = ⟨1⟩
      · refine .inr ⟨.inr ⟨hb.1, ho⟩, ?_⟩
        apply constructorOptionalReturnFinish (by omega) hret
        simpa only [metaMorphoV1_1Creation_block_3791_stack, ho,
          show UInt256.isZero (⟨1⟩ : UInt256) = (⟨0⟩ : UInt256) by decide] using r4
      · have hw := hb.2.resolve_right ho
        have r5 := metaMorphoV1_1Creation_block_3745_taken
          (by simp only [List.length_cons]; omega) (by rw [hw]; decide) (by native_decide) r4
        exact .inl ⟨fun h => ho (h.resolve_left hz).2,
          metaMorphoV1_1Creation_block_3754 (by simp only [List.length_cons]; omega) r5⟩

end Benchmarks.Morpho.MetaMorphoV1_1
