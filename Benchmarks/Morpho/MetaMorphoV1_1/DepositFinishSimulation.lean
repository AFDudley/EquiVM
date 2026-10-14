import Benchmarks.Morpho.MetaMorphoV1_1.DepositFinishSource
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateLastAssetsRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.CheckedArithmetic
import Benchmarks.Morpho.MetaMorphoV1_1.AccrueInterestMemory
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_069
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_066

/-! Checked post-supply accounting and return from the internal deposit helper. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem depositFinishSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr assets ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hc : frame.contract = contract) (hn : frame.locals.get? "lastTotalAssets" = none)
    (ha : frame.locals.get? "assets" = some (uint256Value assets))
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hmem : 96 ≤ mem.size)
    (hs : SourceState s0 I σ evm) (hperm : I.perm = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨14745⟩
      ([assets, ⟨13745⟩, ⟨14753⟩, ret] ++ R) mem aw rdata σ k C) :
    (ExecBlock config frame evm depositFinish .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (mem' : ByteArray), SourceState s0 I evm'.accountMap evm' ∧
      ExecBlock config frame evm depositFinish
        (.returned (depositUpdatedFrame frame) evm' (some [uint256Value ptr])) ∧
      memLoad ⟨64⟩ mem' = ptr ∧ MemoryPrefix mem mem' ptr.toNat ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R mem' aw' rdata evm'.accountMap k' C' := by
  let previous := Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨22⟩
  have hprevious : codeOwnerStorageWord I σ ⟨22⟩ = previous := (hs.storageRead ⟨22⟩).symm
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_14745_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  change RD (deployedRuntime v) I g s0 ⟨12077⟩
    ([codeOwnerStorageWord I σ ⟨22⟩, assets, ⟨13745⟩, ⟨14753⟩, ret] ++ R)
    mem aw1 rdata σ k1 C1 at h1
  rw [hprevious] at h1
  by_cases hfit : previous.toNat + assets.toNat < UInt256.size
  · obtain ⟨k2, C2, h2⟩ := checkedAddReturn v
      (by simp only [List.append, List.length_cons]; omega) hfit
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
    obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_13745_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    rw [hs.accounts, ← hs.env] at h3
    obtain ⟨aw4, k4, C4, h4⟩ := updateLastAssetsReturn v
      (by simp only [List.append, List.length_cons]; omega)
      (by rw [hs.env]; exact hperm) (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h3
    rw [hs.env, hfree] at h4
    obtain ⟨aw5, k5, C5, h5⟩ := metaMorphoV1_1_block_14753_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append]; omega) hret h4
    refine .inr ⟨updateLastAssetsState evm (previous + assets), _, ?_,
      depositFinishSource hc hn ha hp hfit, writeFreeWord_free _ hfree hmem hlo,
      memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _)), aw5, k5, C5, h5⟩
    have hs' := hs.storageWrite ⟨22⟩ (previous + assets)
    rw [hs'.accounts] at hs'
    simpa only [updateLastAssetsState, hs.env] using hs'
  · exact .inl ⟨depositFinishSourceReverts hc hn ha (Nat.le_of_not_gt hfit),
      checkedAddRevert v (by simp only [List.append, List.length_cons]; omega)
        (Nat.le_of_not_gt hfit) h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
