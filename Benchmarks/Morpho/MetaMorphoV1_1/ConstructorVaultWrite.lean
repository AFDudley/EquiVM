import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultStore

/-! Complete vault-string assignment, preserving the allocated constructor buffers. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

theorem constructorVaultScratchPreserved {mem mem' : ByteArray} (symbol : Bool)
    (hmem : 96 ≤ mem.size) (hm : mem' = mem ∨ mem' = stringStorageScratch mem symbol) :
    (∀ limit, ByteMemoryPrefix mem mem' limit) ∧ memLoad ⟨64⟩ mem' = memLoad ⟨64⟩ mem := by
  rcases hm with rfl | rfl
  · exact ⟨fun _ => .refl _ _, rfl⟩
  · exact ⟨fun limit => byteMemoryPrefix_writeWord mem 0 limit _ (.inr (by decide)),
      stringStorageScratch_free mem symbol hmem⟩

theorem constructorVaultWrite {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem rdata bytes : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr : UInt256} (a : ConstructorArgs) (symbol : Bool) (hs : SourceState s0 I σ evm)
    (hperm : I.perm = true)
    (hvalid : storageStringValid (storageStringHeader evm (stringViewSlot symbol)))
    (buffer : StringBuffer mem ptr.toNat bytes) (hlo : 96 ≤ ptr.toNat)
    (hfit : ptr.toNat + 32 + bytes.size < UInt256.size) (hsmall : bytes.size < 2 ^ 64)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultOldPC symbol)
      (storageStringLength (storageStringHeader evm (stringViewSlot symbol)) ::
        UInt256.ofNat bytes.size :: ptr :: constructorVaultTail a symbol) mem aw rdata σ k C) :
    ∃ mem' aw' k' C', StringBuffer mem' ptr.toNat bytes ∧
      (∀ limit, ByteMemoryPrefix mem mem' limit) ∧
      memLoad ⟨64⟩ mem' = memLoad ⟨64⟩ mem ∧
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultEncodePC symbol)
        (ptr :: constructorVaultEventPC symbol :: stringSetTopic symbol :: constructorVaultTail a symbol)
        mem' aw' rdata (storageStringWriteState evm (stringViewSlot symbol) bytes).accountMap k' C' := by
  have hn : (UInt256.ofNat bytes.size).toNat = bytes.size := UInt256.toNat_ofNat_of_lt (by omega)
  obtain ⟨mem1, junk, _, _, _, hm, r1⟩ := constructorVaultClear a symbol hperm
    (storageStringLength_lt _) (by rw [hn]; omega) rd
  rw [hn] at r1
  have hb : StringBuffer mem1 ptr.toNat bytes := by
    rcases hm with rfl | rfl
    · exact buffer
    · exact buffer.storageScratch hlo symbol
  have hsize : 96 ≤ mem.size := by have hsz := buffer.size; omega
  obtain ⟨hp1, hf1⟩ := constructorVaultScratchPreserved symbol hsize hm
  have ha := storageStringWriteState_accounts evm symbol bytes hvalid
  rw [hs.env, ← hs.accounts] at ha
  by_cases hshort : bytes.size < 32
  · obtain ⟨aw2, k2, C2, r2⟩ := constructorVaultShortWrite a symbol hperm hb hfit hshort r1
    rw [if_pos hshort] at ha
    exact ⟨mem1, aw2, k2, C2, hb, hp1, hf1, by rw [ha]; exact r2⟩
  · obtain ⟨aw2, k2, C2, r2⟩ := constructorVaultLongWrite a symbol hperm hb hlo hfit (by omega) hsmall r1
    rw [if_neg hshort] at ha
    obtain ⟨hp2, hf2⟩ := constructorVaultScratchPreserved symbol
      (le_trans hsize (hp1 0).size) (.inr rfl)
    exact ⟨_, aw2, k2, C2, hb.storageScratch hlo symbol,
      fun limit => (hp1 limit).trans (hp2 limit), hf2.trans hf1, by rw [ha]; exact r2⟩

end Benchmarks.Morpho.MetaMorphoV1_1
