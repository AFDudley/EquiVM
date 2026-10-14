import Benchmarks.Morpho.MetaMorphoV1_1.MarketArithmetic
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_032
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_033

/-! The reallocation amount branch and the asset/share choice for a withdrawal. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem reallocateAmountRuntime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {market shares assets assetsPtr allocation target : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hload : memLoad assetsPtr mem = target)
    (rd : RD (deployedRuntime v) I g s0 ⟨6162⟩
      (market :: shares :: assets :: assetsPtr :: allocation :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0
      (if UInt256.ofNat (assets.toNat - target.toNat) = ⟨0⟩ then ⟨6450⟩ else ⟨6182⟩)
      (target :: assets :: shares :: allocation :: assetsPtr ::
        UInt256.ofNat (assets.toNat - target.toNat) :: R) mem aw' rdata σ k' C' := by
  have hm : UInt256.mul (UInt256.sub assets (memLoad assetsPtr mem))
      (UInt256.gt assets (memLoad assetsPtr mem)) = UInt256.ofNat (assets.toNat - target.toNat) := by
    rw [hload, u256_mul_comm, wordZeroFloorSub]
  have hm' : UInt256.mul (UInt256.sub assets target) (UInt256.gt assets target) =
      UInt256.ofNat (assets.toNat - target.toNat) := by rw [u256_mul_comm, wordZeroFloorSub]
  by_cases hz : UInt256.ofNat (assets.toNat - target.toNat) = ⟨0⟩
  · rw [if_pos hz]
    obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_6162_taken_packed
      (immWords := wordsOf (immStore v)) hstack (by rw [hm, hz]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨aw1, k1, C1, by simpa only [metaMorphoV1_1_block_6162_taken_stack, hload, hm'] using h1⟩
  · rw [if_neg hz]
    obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_6162_fallthrough_packed
      (immWords := wordsOf (immStore v)) hstack (by rw [hm]; exact isZero_eq_zero_of_ne hz) rd
    exact ⟨aw1, k1, C1, by simpa only [metaMorphoV1_1_block_6162_fallthrough_stack, hload, hm'] using h1⟩

set_option maxRecDepth 2000 in
theorem reallocateWithdrawSetupRuntime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {target assets shares allocation assetsPtr amount withdrawn id offset i len supplied saved : UInt256}
    {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 13 ≤ 1024)
    (hload : memLoad assetsPtr mem = target)
    (rd : RD (deployedRuntime v) I g s0 ⟨6182⟩
      ([target, assets, shares, allocation, assetsPtr, amount, withdrawn, id, offset, i, len, supplied, saved] ++ R)
      mem aw rdata σ k C) :
    ∃ scratch aw' k' C', RD (deployedRuntime v) I g s0 ⟨6192⟩
      ([scratch, allocation, if target = ⟨0⟩ then shares else ⟨0⟩,
        if target = ⟨0⟩ then ⟨0⟩ else amount, withdrawn, id, offset, i, len, supplied, saved] ++ R)
      mem aw' rdata σ k' C' := by
  by_cases hz : target = ⟨0⟩
  · simp only [if_pos hz]
    obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_6182_taken_packed
      (immWords := wordsOf (immStore v)) (by dsimp only [List.append, List.length_cons, List.length_nil]; omega)
      (by rw [hload, hz]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_6439_packed
      (immWords := wordsOf (immStore v))
      (by dsimp only [List.append, List.length_cons, List.length_nil]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    exact ⟨saved, aw2, k2, C2, h2⟩
  · simp only [if_neg hz]
    obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_6182_fallthrough_packed
      (immWords := wordsOf (immStore v)) (by dsimp only [List.append, List.length_cons, List.length_nil]; omega)
      (by rw [hload]; exact isZero_eq_zero_of_ne hz) rd
    exact ⟨shares, aw1, k1, C1, h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
