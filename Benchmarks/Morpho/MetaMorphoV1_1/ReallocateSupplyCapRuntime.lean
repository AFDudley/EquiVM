import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositQueueRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.CheckedArithmetic
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_033
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_034

/-! The nonzero supply path reads its cap and checks addition before the strict call. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem reallocateSupplyCapRuntime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {assets allocation supplied amount id : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024) (hnz : amount ≠ ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨6479⟩
      (assets :: allocation :: supplied :: amount :: id :: R) mem aw rdata σ k C) :
    ((maxDepositCapWord I σ id).toNat < assets.toNat + amount.toNat ∧ RDrev (deployedRuntime v) g s0) ∨
    (assets.toNat + amount.toNat ≤ (maxDepositCapWord I σ id).toNat ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨6526⟩
        (allocation :: supplied :: amount :: id :: R)
        (twoWordHashMem id ⟨13⟩ mem) aw' rdata σ k' C') := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_6479_fallthrough_packed
    (immWords := wordsOf (immStore v)) (by dsimp only [List.length_cons]; omega)
    (isZero_eq_zero_of_ne hnz) rd
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_6486_packed
    (immWords := wordsOf (immStore v)) hstack
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  have hh : keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem id ⟨13⟩ mem) = solcMappingSlot ⟨13⟩ id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 184 - 1) := rfl
  change RD (deployedRuntime v) I g s0 ⟨12077⟩
    (assets :: amount :: ⟨6520⟩ :: UInt256.land _
      (codeOwnerStorageWord I σ (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem id ⟨13⟩ mem))) ::
      allocation :: supplied :: amount :: id :: R)
    (twoWordHashMem id ⟨13⟩ mem) aw2 rdata σ k2 C2 at h2
  rw [hh, hm, u256_land_comm] at h2
  change RD (deployedRuntime v) I g s0 ⟨12077⟩
    (assets :: amount :: ⟨6520⟩ :: maxDepositCapWord I σ id :: allocation :: supplied :: amount :: id :: R)
    (twoWordHashMem id ⟨13⟩ mem) aw2 rdata σ k2 C2 at h2
  by_cases hfit : assets.toNat + amount.toNat < UInt256.size
  · obtain ⟨k3, C3, h3⟩ := checkedAddReturn v
      (by dsimp only [List.length_cons]; omega) hfit
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2
    have hsum : (assets + amount).toNat = assets.toNat + amount.toNat := addWord_toNat _ _ hfit
    by_cases hcap : assets.toNat + amount.toNat ≤ (maxDepositCapWord I σ id).toNat
    · obtain ⟨aw4, k4, C4, h4⟩ := metaMorphoV1_1_block_6520_fallthrough_packed
        (immWords := wordsOf (immStore v)) (by dsimp only [List.length_cons]; omega)
        (by apply ugt_zero; rwa [hsum]) h3
      exact .inr ⟨hcap, aw4, k4, C4, h4⟩
    · obtain ⟨aw4, k4, C4, h4⟩ := metaMorphoV1_1_block_6520_taken_packed
        (immWords := wordsOf (immStore v)) (by dsimp only [List.length_cons]; omega)
        (by rw [ugt_one (by rw [hsum]; omega)]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
      exact .inl ⟨Nat.lt_of_not_ge hcap, metaMorphoV1_1_block_6724
        (immWords := wordsOf (immStore v)) (by omega) h4⟩
  · exact .inl ⟨lt_of_lt_of_le (maxDepositCapWord I σ id).val.isLt (Nat.le_of_not_gt hfit),
      checkedAddRevert v (by dsimp only [List.length_cons]; omega) (Nat.le_of_not_gt hfit) h2⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
