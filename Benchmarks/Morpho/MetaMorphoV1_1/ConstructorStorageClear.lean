import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStorageLoop
import Benchmarks.Morpho.MetaMorphoV1_1.StringClearStart

/-! Clearing the constructor's old ERC20 metadata, including the short-string path. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

-- LIBRARY CANDIDATE: the data-word clearing performed when assigning an empty string.
def emptyStringClearedAccounts (owner : AccountAddress) (σ : AccountMap) (slot : UInt256)
    (old : Nat) : AccountMap :=
  if old < 32 then σ else
    clearDataWordsForwardFrom owner σ (solidityBytesDataBaseSlot slot) ⟨0⟩
      (solidityBytesDataWordCount old)

def constructorStorageScratch (mem : ByteArray) (symbol : Bool) : ByteArray :=
  writeWord mem 0 (constructorMetadataSlot symbol)

-- LIBRARY CANDIDATE: hashing a slot stored in scratch memory yields its string data base.
theorem storageSlotScratch_hash (mem : ByteArray) (slot : UInt256) :
    keccakWord ⟨0⟩ ⟨32⟩ (writeWord mem 0 slot) = solidityBytesDataBaseSlot slot := by
  unfold solidityBytesDataBaseSlot
  rw [uInt256OfByteArray_eq]
  exact wordAt0Mem_keccak_word slot mem

theorem constructorStorageClearLongStart {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {old : UInt256} (a : ConstructorArgs) (ptr : Nat) (symbol : Bool)
    (hlong : 32 ≤ old.toNat) (hold : old.toNat < 2 ^ 255)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorMetadataClearPC symbol)
      (constructorMetadataPtr ptr symbol :: old :: ⟨0⟩ :: constructorMetadataTail a ptr symbol)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorStorageLoopPC symbol)
      (⟨0⟩ :: solidityBytesDataBaseSlot (constructorMetadataSlot symbol) ::
        UInt256.ofNat (solidityBytesDataWordCount old.toNat) ::
        constructorMetadataPtr ptr symbol :: ⟨0⟩ :: ⟨0⟩ :: constructorMetadataTail a ptr symbol)
      (constructorStorageScratch mem symbol) aw' rdata σ k' C' := by
  have h31 : UInt256.gt old (UInt256.ofNat 31) ≠ ⟨0⟩ := by
    rw [show UInt256.gt old (UInt256.ofNat 31) = ⟨1⟩ from ult_one (by change 31 < old.toNat; omega)]
    decide
  have h0 : UInt256.isZero (UInt256.gt old ⟨0⟩) = ⟨0⟩ := by
    rw [show UInt256.gt old ⟨0⟩ = ⟨1⟩ from ult_one (by change 0 < old.toNat; omega)]
    decide
  have hc : UInt256.shiftRight (UInt256.ofNat 31 + old) (UInt256.ofNat 5) =
      UInt256.ofNat (solidityBytesDataWordCount old.toNat) := by
    rw [u256_add_comm]; exact stringCeilWord old hold
  cases symbol with
  | false =>
    obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_286_taken_packed (by simp [constructorMetadataTail])
      h31 (by native_decide) rd
    obtain ⟨_, _, _, r2⟩ := metaMorphoV1_1Creation_block_2510_fallthrough_packed (by simp [constructorMetadataTail]) h0 r1
    obtain ⟨_, _, _, r3⟩ := metaMorphoV1_1Creation_block_2519_taken_packed (by simp)
      (by decide) (by native_decide) r2
    obtain ⟨_, _, _, r4⟩ := metaMorphoV1_1Creation_block_2590_packed (by simp)
      (by native_decide) r3
    obtain ⟨aw5, k5, C5, r5⟩ := metaMorphoV1_1Creation_block_2544_packed (by simp) r4
    change RD _ I g s0 ⟨2560⟩
      (⟨0⟩ :: (⟨0⟩ + keccakWord ⟨0⟩ ⟨32⟩ (writeWord mem 0 ⟨3⟩)) ::
        UInt256.sub (UInt256.shiftRight (UInt256.ofNat 31 + old) (UInt256.ofNat 5)) ⟨0⟩ ::
        constructorMetadataPtr ptr false :: ⟨0⟩ :: ⟨0⟩ :: constructorMetadataTail a ptr false)
      (constructorStorageScratch mem false) aw5 rdata σ k5 C5 at r5
    rw [u256_zero_add, storageSlotScratch_hash, hc, uint256_sub_zero_right] at r5
    exact ⟨aw5, k5, C5, r5⟩
  | true =>
    obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_382_taken_packed (by simp [constructorMetadataTail])
      h31 (by native_decide) rd
    obtain ⟨_, _, _, r2⟩ := metaMorphoV1_1Creation_block_2298_fallthrough_packed (by simp [constructorMetadataTail]) h0 r1
    obtain ⟨_, _, _, r3⟩ := metaMorphoV1_1Creation_block_2307_taken_packed (by simp)
      (by decide) (by native_decide) r2
    obtain ⟨_, _, _, r4⟩ := metaMorphoV1_1Creation_block_2378_packed (by simp)
      (by native_decide) r3
    obtain ⟨aw5, k5, C5, r5⟩ := metaMorphoV1_1Creation_block_2332_packed (by simp) r4
    change RD _ I g s0 ⟨2348⟩
      (⟨0⟩ :: (⟨0⟩ + keccakWord ⟨0⟩ ⟨32⟩ (writeWord mem 0 ⟨4⟩)) ::
        UInt256.sub (UInt256.shiftRight (UInt256.ofNat 31 + old) (UInt256.ofNat 5)) ⟨0⟩ ::
        constructorMetadataPtr ptr true :: ⟨0⟩ :: ⟨0⟩ :: constructorMetadataTail a ptr true)
      (constructorStorageScratch mem true) aw5 rdata σ k5 C5 at r5
    rw [u256_zero_add, storageSlotScratch_hash, hc, uint256_sub_zero_right] at r5
    exact ⟨aw5, k5, C5, r5⟩

theorem constructorStorageClear {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {old : UInt256} (a : ConstructorArgs) (ptr : Nat) (symbol : Bool)
    (hperm : I.perm = true) (hold : old.toNat < 2 ^ 255)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorMetadataClearPC symbol)
      (constructorMetadataPtr ptr symbol :: old :: ⟨0⟩ :: constructorMetadataTail a ptr symbol)
      mem aw rdata σ k C) :
    ∃ mem' junk aw' k' C', (mem' = mem ∨ mem' = constructorStorageScratch mem symbol) ∧
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorStorageWritePC symbol)
        (junk :: constructorMetadataPtr ptr symbol :: ⟨0⟩ :: ⟨0⟩ :: constructorMetadataTail a ptr symbol)
        mem' aw' rdata
        (emptyStringClearedAccounts I.codeOwner σ (constructorMetadataSlot symbol) old.toNat) k' C' := by
  by_cases hs : old.toNat < 32
  · have hc : UInt256.gt old (UInt256.ofNat 31) = ⟨0⟩ :=
      ult_zero (by change old.toNat ≤ 31; omega)
    have hnext : ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
        (constructorStorageWritePC symbol)
        (old :: constructorMetadataPtr ptr symbol :: ⟨0⟩ :: ⟨0⟩ :: constructorMetadataTail a ptr symbol)
        mem aw' rdata σ k' C' := by
      cases symbol with
      | false => exact metaMorphoV1_1Creation_block_286_fallthrough_packed (by simp [constructorMetadataTail]) hc rd
      | true => exact metaMorphoV1_1Creation_block_382_fallthrough_packed (by simp [constructorMetadataTail]) hc rd
    obtain ⟨aw1, k1, C1, r1⟩ := hnext
    exact ⟨mem, old, aw1, k1, C1, .inl rfl, by
      simpa only [emptyStringClearedAccounts, if_pos hs] using r1⟩
  · obtain ⟨_, _, _, r1⟩ := constructorStorageClearLongStart a ptr symbol (by omega) hold rd
    have hc : solidityBytesDataWordCount old.toNat < UInt256.size := by
      unfold solidityBytesDataWordCount
      change _ < 2 ^ 256
      omega
    obtain ⟨aw2, k2, C2, r2⟩ := constructorStorageLoop symbol
      (solidityBytesDataWordCount old.toNat) 0
      (by cases symbol <;> simp [constructorMetadataTail]) hperm
      (by rw [UInt256.toNat_ofNat_of_lt hc]; omega) r1
    refine ⟨_, UInt256.ofNat (solidityBytesDataWordCount old.toNat), aw2, k2, C2, .inr rfl, ?_⟩
    simpa only [emptyStringClearedAccounts, if_neg hs] using r2

end Benchmarks.Morpho.MetaMorphoV1_1
