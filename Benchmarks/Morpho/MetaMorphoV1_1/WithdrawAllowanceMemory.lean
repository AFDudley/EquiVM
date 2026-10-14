import Benchmarks.Morpho.MetaMorphoV1_1.SpendAllowanceFunction
import Benchmarks.Morpho.MetaMorphoV1_1.MappingScratchMemory

/-! Allowance spending preserves the allocated heap and its free cursor. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem approvalScratchMem_prefix (mem : ByteArray) (owner spender : AccountAddress) (limit : Nat) :
    MemoryPrefix mem (approvalScratchMem mem owner spender) limit :=
  (twoWordHashMem_prefix mem _ _ limit).trans (twoWordHashMem_prefix _ _ _ limit)

theorem approvalScratchMem_free {mem : ByteArray} (owner spender : AccountAddress)
    (hmem : 96 ≤ mem.size) :
    memLoad ⟨64⟩ (approvalScratchMem mem owner spender) = memLoad ⟨64⟩ mem := by
  rw [approvalScratchMem, twoWordHashMem_free _ _
    (le_trans hmem (twoWordHashMem_prefix mem _ _ 0).size), twoWordHashMem_free _ _ hmem]

set_option maxRecDepth 2000 in
theorem withdrawSpendAllowanceReturn {evm : State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {owner spender : AccountAddress} {value ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (hgood : spendAllowanceAllowed evm owner spender value) (hperm : evm.executionEnv.perm = true)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hmem : 96 ≤ mem.size)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨12530⟩
      (UInt256.ofNat owner.toNat :: UInt256.ofNat spender.toNat :: value :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    ∃ mem' aw' k' C', memLoad ⟨64⟩ mem' = ptr ∧ MemoryPrefix mem mem' ptr.toNat ∧
      RD (deployedRuntime v) evm.executionEnv g s0 ret R
        mem' aw' rdata (spendAllowanceState evm owner spender value).accountMap k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := spendAllowanceLookup v
    (by simp only [List.length_cons]; omega) rd
  rw [← allowanceWord_accounts] at h1
  have hp1 := approvalScratchMem_prefix mem owner spender ptr.toNat
  have hf1 := (approvalScratchMem_free owner spender hmem).trans hfree
  by_cases hmax : allowanceWord evm owner spender = unlimitedAllowance
  · rw [if_pos hmax] at h1
    rw [spendAllowanceState, if_pos hmax]
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_12579_packed
      (immWords := wordsOf (immStore v)) (by omega) hret h1
    exact ⟨_, aw2, k2, C2, hf1, hp1, h2⟩
  · rw [if_neg hmax] at h1
    obtain ⟨aw2, k2, C2, h2⟩ := spendAllowanceReachStore v
      (by simp only [List.length_cons]; omega) (hgood.resolve_left hmax) h1
    obtain ⟨aw3, k3, C3, h3⟩ := spendAllowanceStoreReturn v (by omega) hperm hret h2
    rw [spendAllowanceState, if_neg hmax, approvalState, storageStore_accountMap]
    exact ⟨_, aw3, k3, C3,
      (approvalScratchMem_free owner spender (le_trans hmem hp1.size)).trans hf1,
      hp1.trans (approvalScratchMem_prefix _ _ _ _), h3⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
