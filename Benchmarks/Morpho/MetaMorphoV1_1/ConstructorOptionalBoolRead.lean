import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorBoolDecode
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorOptionalBoolFinish
import Benchmarks.Morpho.MetaMorphoV1_1.OptionalBoolSource

/-! Decode the first approval's optional Boolean, preserving failed-call short-circuiting. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

theorem constructorOptionalBoolRead {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr spender token request : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (ok : Bool)
    (hstack : R.length + 12 ≤ 1024) (hout : out.size < 2 ^ 64)
    (hlen : memLoad ptr mem = UInt256.ofNat out.size)
    (hword : 32 ≤ out.size → memLoad (ptr + ⟨32⟩) mem = calldataWord out 0)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1134⟩
      (ptr :: (if ok then ⟨1⟩ else ⟨0⟩) :: spender :: token :: request :: ⟨32⟩ :: ⟨64⟩ :: R)
      mem aw out σ k C) :
    (¬ optionalBoolDecodable ok out ∧ RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    (optionalBoolDecodable ok out ∧ ∃ dummy aw' k' C',
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1140⟩
        (dummy :: (if ok && decide (optionalReturnValid out) then ⟨1⟩ else ⟨0⟩) ::
          spender :: token :: request :: ⟨32⟩ :: ⟨64⟩ :: R) mem aw' out σ k' C') := by
  cases ok with
  | false =>
      obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1Creation_block_1134_fallthrough_packed
        (by simp only [List.length_cons]; omega) rfl rd
      exact .inr ⟨.inl rfl, ptr, aw1, k1, C1, r1⟩
  | true =>
      have r1 := metaMorphoV1_1Creation_block_1134_taken
        (by simp only [List.length_cons]; omega) (by decide) (by native_decide) rd
      by_cases hz : out.size = 0
      · have r2 := metaMorphoV1_1Creation_block_1499_fallthrough
          (by simp only [List.length_cons]; omega) (by rw [hlen, hz]; decide) r1
        obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1Creation_block_1514_packed
          (by simp only [List.length_cons]; omega) (by native_decide) r2
        exact .inr ⟨.inr (.inl hz), ⟨0⟩, aw3, k3, C3, by
          simpa only [metaMorphoV1_1Creation_block_1514_stack,
            metaMorphoV1_1Creation_block_1499_fallthrough_stack, hlen, hz,
            optionalReturnValid, true_or, decide_true, Bool.true_and, if_true] using r3⟩
      · have hn : UInt256.ofNat out.size ≠ ⟨0⟩ := by
          intro he
          have hh := congrArg UInt256.toNat he
          rw [UInt256.toNat_ofNat_of_lt (by change _ < 2 ^ 256; omega)] at hh
          exact hz hh
        have r2 := metaMorphoV1_1Creation_block_1499_taken
          (by simp only [List.length_cons]; omega)
          (by rw [hlen, isZero_eq_zero_of_ne hn]; decide) (by native_decide) r1
        have r3 := metaMorphoV1_1Creation_block_1523
          (by simp only [List.length_cons]; omega) (by native_decide) r2
        simp only [metaMorphoV1_1Creation_block_1523_stack,
          metaMorphoV1_1Creation_block_1499_taken_stack, hlen] at r3
        have hs : UInt256.sub (⟨32⟩ + (ptr + UInt256.ofNat out.size)) (ptr + ⟨32⟩) =
            UInt256.ofNat out.size := by
          rw [← uadd_assoc, u256_add_comm (⟨32⟩ : UInt256) ptr, word_add_sub_left]
        rcases constructorBoolDecode (by simp only [List.length_cons]; omega)
            (by omega) hs hword (by native_decide) r3 with hbad | hgood
        · exact .inl ⟨fun h => hbad.1 ((h.resolve_left (by decide)).resolve_left hz), hbad.2⟩
        · obtain ⟨hb, _, _, _, r4⟩ := hgood
          have r5 := metaMorphoV1_1Creation_block_1539
            (by simp only [List.length_cons]; omega) (by native_decide) r4
          obtain ⟨aw6, k6, C6, r6⟩ := metaMorphoV1_1Creation_block_1514_packed
            (by simp only [List.length_cons]; omega) (by native_decide) r5
          have hw : (if true && decide (optionalReturnValid out) then (⟨1⟩ : UInt256) else ⟨0⟩) =
              calldataWord out 0 := by
            rcases hb.2 with he | he <;> simp [optionalReturnValid, hz, he, hb.1,
              show (⟨0⟩ : UInt256) ≠ ⟨1⟩ by decide]
          exact .inr ⟨.inr (.inr hb), ⟨0⟩, aw6, k6, C6, by
            simpa only [metaMorphoV1_1Creation_block_1514_stack,
              metaMorphoV1_1Creation_block_1539_stack, hw] using r6⟩

theorem constructorOptionalBoolResult {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr spender token request : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (ok : Bool)
    (hstack : R.length + 12 ≤ 1024) (hout : out.size < 2 ^ 64)
    (hlen : memLoad ptr mem = UInt256.ofNat out.size)
    (hword : 32 ≤ out.size → memLoad (ptr + ⟨32⟩) mem = calldataWord out 0)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1134⟩
      (ptr :: (if ok then ⟨1⟩ else ⟨0⟩) :: spender :: token :: request :: ⟨32⟩ :: ⟨64⟩ :: R)
      mem aw out σ k C) :
    (¬ optionalBoolDecodable ok out ∧ RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    (optionalBoolDecodable ok out ∧ ∃ aw' k' C',
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
        (if optionalBoolValue σ token ok out then ⟨1153⟩ else ⟨1420⟩)
        (spender :: token :: request :: ⟨32⟩ :: ⟨64⟩ :: R) mem aw' out σ k' C') := by
  rcases constructorOptionalBoolRead ok hstack hout hlen hword rd with hbad | hgood
  · exact .inl hbad
  · obtain ⟨hv, _, _, _, _, r1⟩ := hgood
    obtain ⟨aw2, k2, C2, r2⟩ := constructorOptionalBoolFinish _
      (by simp only [List.length_cons]; omega) r1
    refine .inr ⟨hv, aw2, k2, C2, ?_⟩
    simpa only [optionalBoolValue, Bool.decide_and, Bool.decide_eq_true, Bool.and_assoc] using r2

end Benchmarks.Morpho.MetaMorphoV1_1
