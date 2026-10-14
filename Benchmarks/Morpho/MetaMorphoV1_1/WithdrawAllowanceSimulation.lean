import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawAllowanceMemory
import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawVaultState
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_071
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_072

/-! Optional allowance spending at the entry to the ERC4626 withdrawal. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem withdrawAllowanceSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr ret assets shares : UInt256} {caller receiver owner : AccountAddress} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 17 ≤ 1024)
    (hl : WithdrawVaultLocals v frame caller receiver owner assets shares ptr)
    (hs : SourceState s0 I σ evm) (hperm : I.perm = true)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hmem : 96 ≤ mem.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨15554⟩
      ([shares, UInt256.ofNat receiver.toNat, UInt256.ofNat caller.toNat, assets,
        UInt256.ofNat owner.toNat, ret] ++ R) mem aw rdata σ k C) :
    (ExecStmt config frame evm erc4626WithdrawAllowance .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (mem' : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      WithdrawVaultLocals v frame' caller receiver owner assets shares ptr ∧
      ExecStmt config frame evm erc4626WithdrawAllowance (.ok frame' evm') ∧
      memLoad ⟨64⟩ mem' = ptr ∧ MemoryPrefix mem mem' ptr.toNat ∧
      ∃ scratch0 scratch1 scratch2 aw' k' C', RD (deployedRuntime v) I g s0 ⟨15580⟩
        ([scratch0, scratch1, scratch2, shares, UInt256.ofNat receiver.toNat, UInt256.ofNat caller.toNat,
          assets, UInt256.ofNat owner.toNat, ret] ++ R) mem' aw' rdata evm'.accountMap k' C' := by
  rcases frame with ⟨c, locals, imms⟩
  have hc := hl.contract
  dsimp only at hc
  subst c
  have htest := withdrawVaultAllowanceCondition (evm := evm) hl
  have hargs := withdrawVaultAllowanceArgs (evm := evm) hl
  have hmc : UInt256.land (UInt256.ofNat caller.toNat)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1)) =
      UInt256.ofNat caller.toNat := solcAddrMask_clean (addressWord_val_canonical caller)
  have hmo : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (UInt256.ofNat owner.toNat) = UInt256.ofNat owner.toNat :=
    solcAddrMask_clean_left (addressWord_val_canonical owner)
  by_cases hne : caller ≠ owner
  · rw [decide_eq_true hne] at htest
    have hw : UInt256.ofNat caller.toNat ≠ UInt256.ofNat owner.toNat := by
      intro heq
      apply hne
      have hh := congrArg (fun w : UInt256 ↦ AccountAddress.ofNat w.toNat) heq
      have hround (a : AccountAddress) : AccountAddress.ofNat (UInt256.ofNat a.val).toNat = a := by
        rw [UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le a.isLt (by decide))]
        exact accountAddress_ofNat_toNat a
      simpa only [Fin.toNat, hround] using hh
    obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_15554_taken_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
      (by rw [hmc, hmo]; exact u256_sub_ne_zero_of_ne hw)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [metaMorphoV1_1_block_15554_taken_stack, hmc, hmo] at h1
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_15801_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    rw [hs.accounts, ← hs.env] at h2
    by_cases hgood : spendAllowanceAllowed evm owner caller shares
    · obtain ⟨mem3, aw3, k3, C3, hfree3, hprefix3, h3⟩ := withdrawSpendAllowanceReturn v
        (by simp only [List.append, List.length_cons]; omega) hgood
        (by rw [hs.env]; exact hperm) hfree hmem
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2
      rw [hs.env] at h3
      obtain ⟨aw4, k4, C4, h4⟩ := metaMorphoV1_1_block_15810_packed
        (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
      exact .inr ⟨spendAllowanceState evm owner caller shares, _, mem3,
        spendAllowanceSourceState hs owner caller shares,
        hl.insert "__c0" .unit (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        ExecStmt.iteTrue htest (ExecBlock.consNormal (spendAllowanceCall hargs hgood) ExecBlock.nil),
        hfree3, hprefix3, ⟨0⟩, shares, ⟨0⟩, aw4, k4, C4, h4⟩
    · exact .inl ⟨ExecStmt.iteTrue htest (ExecBlock.consRevert (spendAllowanceCallReverts hargs hgood)),
        spendAllowanceFunctionRevert v (by simp only [List.append, List.length_cons]; omega) hgood h2⟩
  · rw [decide_eq_false hne] at htest
    have heq := not_ne_iff.mp hne
    obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_15554_fallthrough_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
      (by rw [hmc, hmo, heq]; exact u256_sub_self _) rd
    simp only [metaMorphoV1_1_block_15554_fallthrough_stack, hmc, hmo] at h1
    rw [hs.accounts] at h1
    exact .inr ⟨evm, _, mem, ⟨hs.world, hs.env, rfl⟩, hl, ExecStmt.iteFalse htest ExecBlock.nil,
      hfree, .refl _ _, UInt256.ofNat caller.toNat, shares, UInt256.ofNat owner.toNat, aw1, k1, C1, h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
