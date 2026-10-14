import Benchmarks.Morpho.MetaMorphoV1_1.BurnInternalSource
import Benchmarks.Morpho.MetaMorphoV1_1.AccrueInterestMemory
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_071
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_072

/-! The compiled burn guard, balance debit, and subsequent supply decrease. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def withdrawEventTopic : UInt256 :=
  UInt256.ofNat 113923603527463639014809444807069482138736635533632932454551718384408456251611

def withdrawAfterBurnStack (v : MetaMorphoV1_1Immutables) (caller receiver owner : AccountAddress)
    (assets shares ret : UInt256) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat v._asset.toNat, UInt256.ofNat receiver.toNat, assets, ⟨15753⟩,
    shares, UInt256.ofNat receiver.toNat, ⟨64⟩, withdrawEventTopic,
    UInt256.ofNat caller.toNat, assets, UInt256.ofNat owner.toNat, ret] ++ R

set_option maxRecDepth 2000 in
theorem withdrawBurnRead {evm : State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {caller receiver owner : AccountAddress} {assets shares : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨15590⟩
      ([shares, UInt256.ofNat receiver.toNat, UInt256.ofNat caller.toNat, assets,
        UInt256.ofNat owner.toNat] ++ R) mem aw rdata evm.accountMap k C) :
    (¬ shares.toNat ≤ (balanceWord evm owner).toNat ∧ RDrev (deployedRuntime v) g s0) ∨
    (shares.toNat ≤ (balanceWord evm owner).toNat ∧
      ∃ aw' k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨15609⟩
        ([balanceWord evm owner, shares, UInt256.ofNat receiver.toNat, UInt256.ofNat caller.toNat,
          assets, UInt256.ofNat owner.toNat] ++ R)
        (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨0⟩ mem) aw' rdata evm.accountMap k' C') := by
  have hh : keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨0⟩ mem) =
      balanceSlot owner := twoWordHashMem_solcMappingSlot_any _ _ _
  by_cases hbal : shares.toNat ≤ (balanceWord evm owner).toNat
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_15590_fallthrough_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append]; omega) (by
        change UInt256.lt (codeOwnerStorageWord evm.executionEnv evm.accountMap
          (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨0⟩ mem))) shares = ⟨0⟩
        rw [hh]
        exact ult_zero hbal) rd
    change RD (deployedRuntime v) evm.executionEnv g s0 ⟨15609⟩
      ([codeOwnerStorageWord evm.executionEnv evm.accountMap
        (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨0⟩ mem)),
        shares, UInt256.ofNat receiver.toNat, UInt256.ofNat caller.toNat, assets,
        UInt256.ofNat owner.toNat] ++ R)
      (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨0⟩ mem) aw1 rdata evm.accountMap k1 C1 at h1
    rw [hh] at h1
    exact .inr ⟨hbal, aw1, k1, C1, h1⟩
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_15590_taken_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append]; omega) (by
        change UInt256.lt (codeOwnerStorageWord evm.executionEnv evm.accountMap
          (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (UInt256.ofNat owner.toNat) ⟨0⟩ mem))) shares ≠ ⟨0⟩
        rw [hh]
        change UInt256.lt (balanceWord evm owner) shares ≠ ⟨0⟩
        rw [ult_one (Nat.lt_of_not_ge hbal)]
        decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact .inl ⟨hbal, metaMorphoV1_1_block_15776 (immWords := wordsOf (immStore v))
      (by simp only [metaMorphoV1_1_block_15590_taken_stack, List.append, List.length_cons]; omega) h1⟩

set_option maxRecDepth 2000 in
theorem withdrawBurnStores {evm : State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {caller receiver owner : AccountAddress} {assets shares ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 15 ≤ 1024)
    (hperm : evm.executionEnv.perm = true)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨15609⟩
      ([balanceWord evm owner, shares, UInt256.ofNat receiver.toNat, UInt256.ofNat caller.toNat,
        assets, UInt256.ofNat owner.toNat, ret] ++ R) mem aw rdata evm.accountMap k C) :
    ∃ aw' k' C', RD (deployedRuntime v) evm.executionEnv g s0 ⟨15818⟩
      (withdrawAfterBurnStack v caller receiver owner assets shares ret R)
      (mintReturnMemory mem owner shares) aw' rdata (burnBalanceState evm owner shares).accountMap k' C' := by
  let scratch := twoWordHashMem (UInt256.ofNat owner.toNat) ⟨0⟩ mem
  have hh : keccakWord ⟨0⟩ ⟨64⟩ scratch = balanceSlot owner :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_15609_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega) hperm
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [metaMorphoV1_1_block_15609_stack, wordsOf_immStore__asset] at h1
  change RD (deployedRuntime v) evm.executionEnv g s0 ⟨15818⟩
    (withdrawAfterBurnStack v caller receiver owner assets shares ret R)
    (mintReturnMemory mem owner shares) aw1 rdata
    (sstoreAccountMap evm.executionEnv.codeOwner
      (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap
        (keccakWord ⟨0⟩ ⟨64⟩ scratch) (UInt256.sub (balanceWord evm owner) shares)) ⟨2⟩
      (UInt256.sub (codeOwnerStorageWord evm.executionEnv
        (sstoreAccountMap evm.executionEnv.codeOwner evm.accountMap
          (keccakWord ⟨0⟩ ⟨64⟩ scratch) (UInt256.sub (balanceWord evm owner) shares)) ⟨2⟩) shares)) k1 C1 at h1
  rw [hh] at h1
  refine ⟨aw1, k1, C1, ?_⟩
  simpa only [burnBalanceState, burnSupplyState, balanceDebitState, balanceStore,
    storageStore_accountMap, storageStore_executionEnv, Stele.EVM.storageLoad,
    State.lookupAccount, Account.lookupStorage, codeOwnerStorageWord] using h1

set_option maxRecDepth 2000 in
theorem withdrawBurnSimulation {evm : State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {k C : Nat}
    {caller receiver owner : AccountAddress} {scratch0 scratch1 scratch2 ptr assets shares ret : UInt256}
    {R : List UInt256} (v : MetaMorphoV1_1Immutables) (hstack : R.length + 15 ≤ 1024)
    (hperm : evm.executionEnv.perm = true) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hmem : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat)
    (rd : RD (deployedRuntime v) evm.executionEnv g s0 ⟨15580⟩
      ([scratch0, scratch1, scratch2, shares, UInt256.ofNat receiver.toNat, UInt256.ofNat caller.toNat,
        assets, UInt256.ofNat owner.toNat, ret] ++ R) mem aw rdata evm.accountMap k C) :
    (¬ burnAllowed evm owner shares ∧ RDrev (deployedRuntime v) g s0) ∨
    (burnAllowed evm owner shares ∧ ∃ mem' aw' k' C',
      memLoad ⟨64⟩ mem' = ptr ∧ MemoryPrefix mem mem' ptr.toNat ∧
      RD (deployedRuntime v) evm.executionEnv g s0 ⟨15818⟩
        (withdrawAfterBurnStack v caller receiver owner assets shares ret R)
        mem' aw' rdata (burnBalanceState evm owner shares).accountMap k' C') := by
  by_cases ho : owner ≠ AccountAddress.ofNat 0
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_15580_fallthrough_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
      (isZero_eq_zero_of_ne (approvalAddressWord_ne_zero ho)) rd
    rcases withdrawBurnRead v (by simp only [List.append, List.length_cons]; omega) h1 with
      ⟨hbad, hrev⟩ | ⟨hgood, aw2, k2, C2, h2⟩
    · exact .inl ⟨fun h ↦ hbad h.2, hrev⟩
    obtain ⟨aw3, k3, C3, h3⟩ := withdrawBurnStores v hstack hperm h2
    have hp1 := twoWordHashMem_prefix mem (UInt256.ofNat owner.toNat) ⟨0⟩ ptr.toNat
    have hf1 := (twoWordHashMem_free (UInt256.ofNat owner.toNat) ⟨0⟩ hmem).trans hfree
    exact .inr ⟨⟨ho, hgood⟩, _, aw3, k3, C3,
      mintReturnMemory_free owner shares hf1 (le_trans hmem hp1.size) hlo,
      hp1.trans (mintReturnMemory_prefix owner shares hf1 (le_trans hmem hp1.size)), h3⟩
  · have hz := not_ne_iff.mp ho
    subst owner
    obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_15580_taken_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
      (by decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact .inl ⟨fun h ↦ h.1 rfl, metaMorphoV1_1_block_12898 (immWords := wordsOf (immStore v))
      (by simp only [metaMorphoV1_1_block_15580_taken_stack, List.append, List.length_cons]; omega) h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
