import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorCallReturn
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_017

/-! The optional decimals query accepts only a successful, complete uint8-valued word. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

def constructorDecimalsValid (ok : Bool) (out : ByteArray) : Prop :=
  ok = true ∧ 32 ≤ out.size ∧ (calldataWord out 0).toNat ≤ 255

instance (ok : Bool) (out : ByteArray) : Decidable (constructorDecimalsValid ok out) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def constructorDecimalsWord (ok : Bool) (out : ByteArray) : UInt256 :=
  if constructorDecimalsValid ok out then calldataWord out 0 else ⟨0⟩

theorem constructorDecimalsResult {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256} (ok : Bool)
    (hstack : R.length + 7 ≤ 1024) (hout : out.size < 2 ^ 255)
    (hload : memLoad ptr mem = UInt256.ofNat out.size)
    (hword : 32 ≤ out.size → memLoad (UInt256.ofNat 32 + ptr) mem = calldataWord out 0)
    (hret : (D_J metaMorphoV1_1CreationBytecode 0).contains ret = true)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨3602⟩
      (ptr :: (if ok then ⟨1⟩ else ⟨0⟩) :: ret :: R) mem aw out σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ret
      (constructorDecimalsWord ok out :: (if constructorDecimalsValid ok out then ⟨1⟩ else ⟨0⟩) :: R)
      mem aw' out σ k' C' := by
  cases ok with
  | false =>
    have r1 := metaMorphoV1_1Creation_block_3602_fallthrough
      (by simp only [List.length_cons]; omega) rfl rd
    have r2 := metaMorphoV1_1Creation_block_3609_fallthrough
      (by simp only [List.length_cons]; omega) rfl r1
    obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1Creation_block_3614_packed (by omega) hret r2
    refine ⟨aw3, k3, C3, ?_⟩
    simpa only [constructorDecimalsWord, constructorDecimalsValid, Bool.false_eq_true,
      false_and, if_false, metaMorphoV1_1Creation_block_3614_stack] using r3
  | true =>
    have r1 := metaMorphoV1_1Creation_block_3602_taken
      (by simp only [List.length_cons]; omega) (by decide) (by native_decide) rd
    obtain ⟨_, _, _, r2⟩ := metaMorphoV1_1Creation_block_3656_packed
      (by simp only [List.length_cons]; omega) (by native_decide) r1
    simp only [metaMorphoV1_1Creation_block_3656_stack, hload] at r2
    by_cases hl : 32 ≤ out.size
    · have hc : UInt256.isZero (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32)) = ⟨1⟩ := by
        rw [ult_zero (by rw [UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign hout)]; exact hl)]
        rfl
      rw [hc] at r2
      have r3 := metaMorphoV1_1Creation_block_3609_taken
        (by simp only [List.length_cons]; omega) (by decide) (by native_decide) r2
      have hguard : UInt256.slt (UInt256.sub (ptr + memLoad ptr mem) ptr) (UInt256.ofNat 32) = ⟨0⟩ := by
        rw [word_add_sub_left, hload]
        exact slt_ofNat_lit_zero (by decide) hl hout
      have r4 := metaMorphoV1_1Creation_block_3621_fallthrough
        (by simp only [List.length_cons]; omega) hguard r3
      by_cases hv : (calldataWord out 0).toNat ≤ 255
      · have hgood : constructorDecimalsValid true out := ⟨rfl, hl, hv⟩
        have r5 := metaMorphoV1_1Creation_block_3635_fallthrough
          (by simp only [List.length_cons]; omega)
          (by rw [hword hl]; exact ugt_zero hv) r4
        obtain ⟨aw6, k6, C6, r6⟩ := metaMorphoV1_1Creation_block_3647_packed (by omega) hret r5
        have hclean : (calldataWord out 0).land (UInt256.ofNat 255) = calldataWord out 0 :=
          lowByteClean (by omega)
        refine ⟨aw6, k6, C6, ?_⟩
        simpa only [constructorDecimalsWord, if_pos hgood,
          metaMorphoV1_1Creation_block_3647_stack,
          metaMorphoV1_1Creation_block_3635_fallthrough_stack,
          hword hl, hclean] using r6
      · have hbad : ¬ constructorDecimalsValid true out := fun h => hv h.2.2
        have r5 := metaMorphoV1_1Creation_block_3635_taken
          (by simp only [List.length_cons]; omega)
          (by rw [hword hl, ugt_one (by change 255 < (calldataWord out 0).toNat; omega)]; decide)
          (by native_decide) r4
        obtain ⟨aw6, k6, C6, r6⟩ := metaMorphoV1_1Creation_block_3614_packed (by omega) hret r5
        refine ⟨aw6, k6, C6, ?_⟩
        simpa only [constructorDecimalsWord, if_neg hbad, metaMorphoV1_1Creation_block_3614_stack] using r6
    · have hbad : ¬ constructorDecimalsValid true out := fun h => hl h.2.1
      have hc : UInt256.isZero (UInt256.lt (UInt256.ofNat out.size) (UInt256.ofNat 32)) = ⟨0⟩ := by
        have hlt : (UInt256.ofNat out.size).toNat < (UInt256.ofNat 32).toNat := by
          rw [UInt256.toNat_ofNat_of_lt (lt_size_of_lt_sign hout)]
          change out.size < 32
          omega
        rw [ult_one hlt]
        rfl
      rw [hc] at r2
      have r3 := metaMorphoV1_1Creation_block_3609_fallthrough
        (by simp only [List.length_cons]; omega) rfl r2
      obtain ⟨aw4, k4, C4, r4⟩ := metaMorphoV1_1Creation_block_3614_packed (by omega) hret r3
      refine ⟨aw4, k4, C4, ?_⟩
      simpa only [constructorDecimalsWord, if_neg hbad, metaMorphoV1_1Creation_block_3614_stack] using r4

end Benchmarks.Morpho.MetaMorphoV1_1
