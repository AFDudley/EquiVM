import Benchmarks.Morpho.MetaMorphoV1_1.MulticallInitLoop
import Benchmarks.Morpho.MetaMorphoV1_1.WordArraySizeRuntime

/-! Allocate and initialize multicall's result array before the first delegated call. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: normalize the signed tail-access bound computed with NOT 30.
theorem add_lnot30_sub31 (w : UInt256) :
    w + UInt256.lnot (UInt256.ofNat 30) = w - (⟨31⟩ : UInt256) := by
  have hnot : (UInt256.lnot (UInt256.ofNat 30)).toNat = UInt256.size - 31 := by decide +kernel
  have hb : w.toNat < UInt256.size := w.val.isLt
  have hs : 31 ≤ UInt256.size := by decide +kernel
  apply u256_inj
  change (w + UInt256.lnot (UInt256.ofNat 30)).toNat = (UInt256.sub w ⟨31⟩).toNat
  rw [uadd_toNat, hnot]
  by_cases hw : 31 ≤ w.toNat
  · rw [usub_toNat (a := w) (b := (⟨31⟩ : UInt256)) hw]
    change (w.toNat + (UInt256.size - 31)) % UInt256.size = w.toNat - 31
    rw [show w.toNat + (UInt256.size - 31) = (w.toNat - 31) + UInt256.size by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · rw [usub_toNat_underflow (by change w.toNat < 31; omega)]
    change (w.toNat + (UInt256.size - 31)) % UInt256.size = UInt256.size + w.toNat - 31
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

theorem multicallAllocate {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C n : Nat}
    {base : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (hstack : R.length + 12 ≤ 1024) (hn : n ≤ solcMaxU64)
    (hfree : memLoad ⟨64⟩ mem = ⟨128⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨3814⟩ (UInt256.ofNat n :: base :: R)
      mem aw out σ k C) :
    (¬ 160 + 32 * n < 2 ^ 64 ∧ RDrev (deployedRuntime v) g s0) ∨
    (160 + 32 * n < 2 ^ 64 ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨3877⟩
        (⟨0⟩ :: base :: ((UInt256.ofNat I.calldata.size - base) - ⟨31⟩) ::
          UInt256.ofNat n :: ⟨128⟩ :: R)
        (multicallInitialMemory mem n) aw' out σ k' C') := by
  have hn' : n < UInt256.size := lt_of_le_of_lt hn (by decide)
  have hnw : (UInt256.ofNat n).toNat ≤ solcMaxU64 := by
    rwa [UInt256.toNat_ofNat_of_lt hn']
  have r1 := metaMorphoV1_1_block_3814 (immWords := wordsOf (immStore v))
    (by omega) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨k2, C2, r2⟩ := wordArraySizeReturn v
    (by simp only [List.length_cons]; omega) hnw
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1
  rw [UInt256.toNat_ofNat_of_lt hn'] at r2
  have r3 := metaMorphoV1_1_block_3824 (immWords := wordsOf (immStore v))
    (by omega) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
  change RD (deployedRuntime v) I g s0 ⟨11329⟩
    (memLoad ⟨64⟩ mem :: UInt256.ofNat (32 + 32 * n) :: ⟨3838⟩ :: UInt256.ofNat n ::
      base :: memLoad ⟨64⟩ mem :: R) mem _ out σ _ _ at r3
  rw [hfree] at r3
  by_cases hf : 160 + 32 * n < 2 ^ 64
  case neg =>
    exact .inl ⟨hf, allocateRoundedRevert v (by simp only [List.length_cons]; omega)
      (by rw [wordArrayAllocationFits _ hn]; exact hf) r3⟩
  obtain ⟨aw4, k4, C4, r4⟩ := allocateRoundedReturn v
    (by simp only [List.length_cons]; omega) ((wordArrayAllocationFits ⟨128⟩ hn).mpr hf)
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r3
  rw [wordArrayNextCursor _ hn] at r4
  obtain ⟨aw5, k5, C5, r5⟩ := metaMorphoV1_1_block_3838_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r4
  have r5' : RD (deployedRuntime v) I g s0 ⟨12021⟩
      (UInt256.ofNat n :: ⟨3853⟩ :: UInt256.lnot ⟨31⟩ :: UInt256.ofNat n :: base :: ⟨128⟩ :: R)
      (wordArrayInitMemory mem ⟨128⟩ n) aw5 out σ k5 C5 := r5
  obtain ⟨k6, C6, r6⟩ := wordArraySizeReturn v
    (by simp only [List.length_cons]; omega) hnw
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r5'
  rw [UInt256.toNat_ofNat_of_lt hn'] at r6
  have r7 := metaMorphoV1_1_block_3853 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) r6
  have hd : UInt256.ofNat (32 + 32 * n) + UInt256.lnot ⟨31⟩ = UInt256.ofNat (32 * n) := by
    apply u256_inj
    rw [wordArrayDataSize hn, UInt256.toNat_ofNat_of_lt (by have := wordArraySize_lt hn; omega)]
  simp only [metaMorphoV1_1_block_3853_stack, hd] at r7
  obtain ⟨aw8, k8, C8, r8⟩ := multicallInitLoop v n (by omega)
    (lt_trans hf (by decide)) (Nat.zero_add n).symm r7
  have r9 := metaMorphoV1_1_block_3864 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) r8
  refine .inr ⟨hf, aw8, k8 + 12, C8 + 32, ?_⟩
  simpa only [metaMorphoV1_1_block_3864_stack, add_lnot30_sub31, multicallInitialMemory,
    Benchmarks.EAS.Attester.wordArrayMemory, wordArrayInitMemory_eq_header,
    show (⟨128⟩ : UInt256).toNat = 128 from rfl, Nat.mul_zero, Nat.add_zero] using r9

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
