import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateCalldataChecks
import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_030
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_031

/-! Nonpayable and calldata validation paths for reallocation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

open Benchmarks.EAS.Attester (arrayHead arrayHead_toNat arrayData_eq_ofNat)

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem reallocateNonpayable {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 2 ≤ 1024)
    (hwv : I.weiValue ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨5836⟩ R mem aw out σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have h := metaMorphoV1_1_block_5836_taken (immWords := wordsOf (immStore v))
    hstack hwv (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) hstack h

theorem reallocateDecodeRuntime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hwv : I.weiValue = ⟨0⟩) (h4 : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨5836⟩ R mem aw out σ k C) :
    (¬ ReallocateCalldataChecks I.calldata ∧ RDrev (deployedRuntime v) g s0) ∨
    (ReallocateCalldataChecks I.calldata ∧ ∃ k' C',
      RD (deployedRuntime v) I g s0 ⟨5916⟩
        (reallocateCount I.calldata :: calldataWord I.calldata 4 :: R)
        mem aw out σ k' C') := by
  have r1 := metaMorphoV1_1_block_5836_fallthrough (immWords := wordsOf (immStore v))
    (by omega) hwv rd
  have hbad
      (hc : UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ ≠ ⟨0⟩) :
      RDrev (deployedRuntime v) g s0 := by
    have h := metaMorphoV1_1_block_5842_taken (immWords := wordsOf (immStore v))
      (by omega) hc (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
    exact metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v)) (by omega) h
  by_cases hhead : 36 ≤ I.calldata.size
  case neg =>
    refine .inl ⟨fun hc ↦ hhead hc.head, hbad ?_⟩
    rw [calldataNot3_eq_sub h4 hsize,
      solcDecodeLenCheckShort_4_32 h4 (by omega) hsize]
    decide
  by_cases hhi : I.calldata.size < 2 ^ 255 + 4
  case neg =>
    refine .inl ⟨fun hc ↦ hhi (by have h := hc.high; omega), hbad ?_⟩
    rw [calldataNot3_eq_sub h4 hsize,
      solcDecodeLenCheckHuge_4_32 (by omega) hsize]
    decide
  have r2 := metaMorphoV1_1_block_5842_fallthrough (immWords := wordsOf (immStore v))
    (by omega) (by
      change UInt256.slt (UInt256.lnot ⟨3⟩ + UInt256.ofNat I.calldata.size) ⟨32⟩ = ⟨0⟩
      rw [calldataNot3_eq_sub h4 hsize]
      exact solcDecodeLenCheckOk_4_32 hhead hhi hsize) r1
  by_cases hoff : (calldataWord I.calldata 4).toNat ≤ solcMaxU64
  case neg =>
    have h := metaMorphoV1_1_block_5854_taken (immWords := wordsOf (immStore v))
      (by omega) (by
        rw [ugt_one (by change solcMaxU64 < (calldataWord I.calldata 4).toNat; omega)]
        decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
    exact .inl ⟨fun hc ↦ hoff hc.offset,
      metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_5854_taken_stack, List.length_cons]; omega) h⟩
  have r3 := metaMorphoV1_1_block_5854_fallthrough (immWords := wordsOf (immStore v))
    (by omega) (ugt_zero hoff) r2
  change RD _ _ _ _ ⟨5871⟩ (calldataWord I.calldata 4 :: R) _ _ _ _ _ _ at r3
  by_cases hheader : I.calldata.size < 2 ^ 255 ∧
      (calldataWord I.calldata 4).toNat + 36 ≤ I.calldata.size
  case neg =>
    have hzero : UInt256.slt (calldataWord I.calldata 4 + UInt256.ofNat 35)
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
      by_contra hn
      exact hheader ((reallocateHeaderWordCheck hoff hsize).mp hn)
    have r4 := metaMorphoV1_1_block_5871_taken (immWords := wordsOf (immStore v))
      (by omega) (by rw [hzero]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r3
    exact .inl ⟨fun hc ↦ hheader ⟨hc.high, by have := hc.extent; omega⟩,
      metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) r4⟩
  have r4 := metaMorphoV1_1_block_5871_fallthrough (immWords := wordsOf (immStore v))
    (by omega)
    (isZero_eq_zero_of_ne ((reallocateHeaderWordCheck hoff hsize).mpr hheader)) r3
  by_cases hlen : (reallocateCount I.calldata).toNat ≤ solcMaxU64
  case neg =>
    have r5 := metaMorphoV1_1_block_5882_taken (immWords := wordsOf (immStore v))
      (by omega)
      (by rw [ugt_one (by change solcMaxU64 < (reallocateCount I.calldata).toNat; omega)]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r4
    exact .inl ⟨fun hc ↦ hlen hc.length,
      metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_5882_taken_stack, List.length_cons]; omega) r5⟩
  have r5 := metaMorphoV1_1_block_5882_fallthrough (immWords := wordsOf (immStore v))
    (by omega) (ugt_zero hlen) r4
  change RD _ _ _ _ ⟨5901⟩
    (reallocateCount I.calldata :: calldataWord I.calldata 4 :: R) _ _ _ _ _ _ at r5
  by_cases hextent : (calldataWord I.calldata 4).toNat + 36 +
      192 * (reallocateCount I.calldata).toNat ≤ I.calldata.size
  · have r6 := metaMorphoV1_1_block_5901_fallthrough (immWords := wordsOf (immStore v))
      (by omega)
      (by apply ugt_zero
          rw [reallocateExtent_toNat _ _ hoff hlen, UInt256.toNat_ofNat_of_lt hsize]
          exact hextent) r5
    exact .inr ⟨⟨hhead, hheader.1, hoff, hlen, hextent⟩, _, _, r6⟩
  · have r6 := metaMorphoV1_1_block_5901_taken (immWords := wordsOf (immStore v))
      (by omega)
      (by rw [ugt_one (by
            rw [reallocateExtent_toNat _ _ hoff hlen, UInt256.toNat_ofNat_of_lt hsize]
            exact Nat.lt_of_not_ge hextent)]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r5
    exact .inl ⟨fun hc ↦ hextent hc.extent,
      metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega) r6⟩

end Benchmarks.Morpho.MetaMorphoV1_1
