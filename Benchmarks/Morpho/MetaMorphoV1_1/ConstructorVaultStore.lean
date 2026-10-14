import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultLongTail

/-! Packed and long vault metadata stores converge at the event encoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

theorem constructorVaultShortWrite {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata bytes : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {junk ptr : UInt256} (a : ConstructorArgs) (symbol : Bool) (hperm : I.perm = true)
    (buffer : StringBuffer mem ptr.toNat bytes)
    (hfit : ptr.toNat + 32 + bytes.size < UInt256.size) (hshort : bytes.size < 32)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultStorePC symbol)
      (junk :: UInt256.ofNat bytes.size :: ptr :: constructorVaultTail a symbol) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultEncodePC symbol)
      (ptr :: constructorVaultEventPC symbol :: stringSetTopic symbol :: constructorVaultTail a symbol)
      mem aw' rdata (sstoreAccountMap I.codeOwner σ (stringViewSlot symbol)
        (solidityShortBytesWord bytes)) k' C' := by
  obtain ⟨junk1, word, _, _, _, hw, r1⟩ := constructorVaultShortReady a symbol buffer hfit hshort rd
  have hnext : ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorVaultEncodePC symbol)
      (ptr :: constructorVaultEventPC symbol :: stringSetTopic symbol :: constructorVaultTail a symbol)
      mem aw' rdata (sstoreAccountMap I.codeOwner σ (stringViewSlot symbol)
        (stringPackedHeader word (UInt256.ofNat bytes.size))) k' C' := by
    cases symbol with
    | false => exact metaMorphoV1_1Creation_block_854_packed (by simp [constructorVaultTail]) hperm r1
    | true => exact metaMorphoV1_1Creation_block_979_packed (by simp [constructorVaultTail]) hperm r1
  simpa only [hw] using hnext

theorem constructorVaultLongStart {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {junk len ptr : UInt256} (a : ConstructorArgs) (symbol : Bool) (hlong : 32 ≤ len.toNat)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultStorePC symbol)
      (junk :: len :: ptr :: constructorVaultTail a symbol) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultDataLoopPC symbol)
      (⟨0⟩ :: UInt256.land len (UInt256.lnot ⟨31⟩) :: ⟨32⟩ ::
        solidityBytesDataSlot (stringViewSlot symbol) 0 :: len :: ptr :: constructorVaultTail a symbol)
      (stringStorageScratch mem symbol) aw' rdata σ k' C' := by
  have hc : UInt256.eq (UInt256.ofNat 1) (UInt256.gt len (UInt256.ofNat 31)) ≠ ⟨0⟩ := by
    change UInt256.eq ⟨1⟩ (UInt256.lt ⟨31⟩ len) ≠ ⟨0⟩
    rw [ult_one (by change 31 < len.toNat; omega)]; decide
  have hs : solidityBytesDataSlot (stringViewSlot symbol) 0 =
      solidityBytesDataBaseSlot (stringViewSlot symbol) := by
    rw [solidityBytesDataSlot, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_add_zero]
  rw [hs]
  cases symbol with
  | false =>
    obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_813_taken_packed
      (by simp) hc (by native_decide) rd
    obtain ⟨aw2, k2, C2, r2⟩ := metaMorphoV1_1Creation_block_1885_packed (by simp) r1
    change RD _ I g s0 ⟨1901⟩
      (⟨0⟩ :: UInt256.land len (UInt256.lnot ⟨31⟩) :: ⟨32⟩ ::
        keccakWord ⟨0⟩ ⟨32⟩ (writeWord mem 0 ⟨24⟩) :: len :: ptr :: constructorVaultTail a false)
      (stringStorageScratch mem false) aw2 rdata σ k2 C2 at r2
    rw [storageSlotScratch_hash] at r2
    exact ⟨aw2, k2, C2, r2⟩
  | true =>
    obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_938_taken_packed
      (by simp) hc (by native_decide) rd
    obtain ⟨aw2, k2, C2, r2⟩ := metaMorphoV1_1Creation_block_1628_packed (by simp) r1
    change RD _ I g s0 ⟨1644⟩
      (⟨0⟩ :: UInt256.land len (UInt256.lnot ⟨31⟩) :: ⟨32⟩ ::
        keccakWord ⟨0⟩ ⟨32⟩ (writeWord mem 0 ⟨25⟩) :: len :: ptr :: constructorVaultTail a true)
      (stringStorageScratch mem true) aw2 rdata σ k2 C2 at r2
    rw [storageSlotScratch_hash] at r2
    exact ⟨aw2, k2, C2, r2⟩

theorem constructorVaultLongWrite {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata bytes : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {junk ptr : UInt256} (a : ConstructorArgs) (symbol : Bool) (hperm : I.perm = true)
    (buffer : StringBuffer mem ptr.toNat bytes) (hlo : 96 ≤ ptr.toNat)
    (hfit : ptr.toNat + 32 + bytes.size < UInt256.size)
    (hlong : 32 ≤ bytes.size) (hsmall : bytes.size < 2 ^ 64)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultStorePC symbol)
      (junk :: UInt256.ofNat bytes.size :: ptr :: constructorVaultTail a symbol) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultEncodePC symbol)
      (ptr :: constructorVaultEventPC symbol :: stringSetTopic symbol :: constructorVaultTail a symbol)
      (stringStorageScratch mem symbol) aw' rdata (sstoreAccountMap I.codeOwner
        (solidityDataWordsForwardFrom I.codeOwner σ (stringViewSlot symbol) bytes 0
          (solidityBytesDataWordCount bytes.size))
        (stringViewSlot symbol) (solidityBytesHeaderWord bytes.size)) k' C' := by
  have hn : (UInt256.ofNat bytes.size).toNat = bytes.size := UInt256.toNat_ofNat_of_lt (by omega)
  obtain ⟨_, _, _, r1⟩ := constructorVaultLongStart a symbol (by omega) rd
  have hb := buffer.storageScratch hlo symbol
  obtain ⟨_, _, _, r2⟩ := constructorVaultDataWords a symbol (bytes.size / 32) 0
    hperm hb hfit (by omega) (by rw [longDataCutoff_toNat, hn]; omega) r1
  simp only [Nat.zero_add] at r2
  exact constructorVaultDataFinish a symbol hperm hb hfit hlong hsmall r2

end Benchmarks.Morpho.MetaMorphoV1_1
