import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStorageClear
import Benchmarks.Morpho.MetaMorphoV1_1.StringWriteState
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_003

/-! The two initial empty-string stores agree with the source storage backend. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

-- LIBRARY CANDIDATE: account-map semantics of an empty Solidity string assignment.
theorem storageStringWriteEmpty_accounts (evm : State) (slot : UInt256)
    (hvalid : storageStringValid (storageStringHeader evm slot)) :
    (storageStringWriteState evm slot ByteArray.empty).accountMap =
      sstoreAccountMap evm.executionEnv.codeOwner
        (emptyStringClearedAccounts evm.executionEnv.codeOwner evm.accountMap slot
          (storageStringLength (storageStringHeader evm slot)).toNat)
        slot (solidityShortBytesWord ByteArray.empty) := by
  have hp := storageStringPacked evm slot hvalid
  by_cases ho : (storageStringLength (storageStringHeader evm slot)).toNat < 32
  all_goals simp [storageStringWriteState, emptyStringClearedAccounts, hp, ho,
    storageStore_accountMap, clearSolidityBytesDataWordsFrom_executionEnv,
    clearSolidityBytesDataWordsFrom_accountMap, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl]

def constructorStorageDonePC (symbol : Bool) : UInt256 := if symbol then ⟨434⟩ else ⟨338⟩

theorem constructorStorageWrite {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {junk : UInt256} (a : ConstructorArgs) (ptr : Nat) (symbol : Bool) (hperm : I.perm = true)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorStorageWritePC symbol)
      (junk :: constructorMetadataPtr ptr symbol :: ⟨0⟩ :: ⟨0⟩ :: constructorMetadataTail a ptr symbol)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorStorageDonePC symbol) (constructorMetadataTail a ptr symbol) mem aw' rdata
      (sstoreAccountMap I.codeOwner σ (constructorMetadataSlot symbol)
        (solidityShortBytesWord ByteArray.empty)) k' C' := by
  cases symbol with
  | false =>
    obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_296_fallthrough_packed (by simp) (by decide) rd
    obtain ⟨_, _, _, r2⟩ := metaMorphoV1_1Creation_block_311_fallthrough_packed (by simp) rfl r1
    obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1Creation_block_317_packed (by simp) hperm r2
    change RD _ I g s0 ⟨338⟩ (constructorMetadataTail a ptr false) mem aw3 rdata
      (sstoreAccountMap I.codeOwner σ ⟨3⟩ (stringPackedHeader ⟨0⟩ ⟨0⟩)) k3 C3 at r3
    rw [stringPackedHeader_empty] at r3
    exact ⟨aw3, k3, C3, r3⟩
  | true =>
    obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_392_fallthrough_packed (by simp) (by decide) rd
    obtain ⟨_, _, _, r2⟩ := metaMorphoV1_1Creation_block_407_fallthrough_packed (by simp) rfl r1
    obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1Creation_block_413_packed (by simp) hperm r2
    change RD _ I g s0 ⟨434⟩ (constructorMetadataTail a ptr true) mem aw3 rdata
      (sstoreAccountMap I.codeOwner σ ⟨4⟩ (stringPackedHeader ⟨0⟩ ⟨0⟩)) k3 C3 at r3
    rw [stringPackedHeader_empty] at r3
    exact ⟨aw3, k3, C3, r3⟩

theorem constructorInitializeMetadata {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (ptr : Nat) (symbol : Bool)
    (hs : SourceState s0 I σ evm) (hperm : I.perm = true)
    (hvalid : storageStringValid (storageStringHeader evm (constructorMetadataSlot symbol)))
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorMetadataClearPC symbol)
      (constructorMetadataPtr ptr symbol ::
        storageStringLength (solcSlotWord σ I (constructorMetadataSlot symbol)) ::
        ⟨0⟩ :: constructorMetadataTail a ptr symbol) mem aw rdata σ k C) :
    ∃ mem' aw' k' C', (mem' = mem ∨ mem' = constructorStorageScratch mem symbol) ∧
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorStorageDonePC symbol)
        (constructorMetadataTail a ptr symbol) mem' aw' rdata
        (storageStringWriteState evm (constructorMetadataSlot symbol) ByteArray.empty).accountMap k' C' := by
  obtain ⟨mem', junk, _, _, _, hm, r1⟩ := constructorStorageClear a ptr symbol hperm
    (storageStringLength_lt _) rd
  obtain ⟨aw2, k2, C2, r2⟩ := constructorStorageWrite a ptr symbol hperm r1
  refine ⟨mem', aw2, k2, C2, hm, ?_⟩
  rw [storageStringWriteEmpty_accounts evm _ hvalid, hs.env, ← hs.accounts]
  rw [show storageStringHeader evm (constructorMetadataSlot symbol) =
    solcSlotWord σ I (constructorMetadataSlot symbol) from hs.storageRead _]
  exact r2

end Benchmarks.Morpho.MetaMorphoV1_1
