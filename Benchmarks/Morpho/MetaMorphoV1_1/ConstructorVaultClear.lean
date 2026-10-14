import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultClearStart
import Benchmarks.Morpho.MetaMorphoV1_1.StringWriteState

/-! Complete the old vault-string clearing prefix for either metadata field. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

theorem constructorVaultClear {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {old len ptr : UInt256} (a : ConstructorArgs) (symbol : Bool)
    (hperm : I.perm = true) (hold : old.toNat < 2 ^ 255) (hsmall : len.toNat < 2 ^ 255)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultOldPC symbol)
      (old :: len :: ptr :: constructorVaultTail a symbol) mem aw rdata σ k C) :
    ∃ mem' junk aw' k' C', (mem' = mem ∨ mem' = stringStorageScratch mem symbol) ∧
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultStorePC symbol)
        (junk :: len :: ptr :: constructorVaultTail a symbol) mem' aw' rdata
        (stringClearedAccounts I.codeOwner σ symbol old.toNat len.toNat) k' C' := by
  rcases constructorVaultClearDispatch symbol
      (by cases symbol <;> simp [constructorVaultTail]) rd with
    ⟨hskip, aw1, k1, C1, r1⟩ | ⟨hlong, hshrink, aw1, k1, C1, r1⟩
  · have ha : stringClearedAccounts I.codeOwner σ symbol old.toNat len.toNat = σ := by
      unfold stringClearedAccounts
      split
      · rfl
      · have hle : old.toNat ≤ len.toNat := hskip.resolve_left ‹_›
        have hn : ¬ len.toNat < 32 := by omega
        simp only [stringFirstClearedWord, if_neg hn]
        have hc : solidityBytesDataWordCount old.toNat - solidityBytesDataWordCount len.toNat =
            0 := by unfold solidityBytesDataWordCount; omega
        rw [hc]; rfl
    exact ⟨mem, old, aw1, k1, C1, .inl rfl, by rw [ha]; exact r1⟩
  · obtain ⟨_, _, _, r2⟩ := constructorVaultClearInit a symbol hold hsmall (by omega) r1
    have hcount : solidityBytesDataWordCount old.toNat - stringFirstClearedWord len.toNat <
        UInt256.size := by
      unfold solidityBytesDataWordCount
      change _ < 2 ^ 256
      omega
    obtain ⟨aw3, k3, C3, r3⟩ := constructorVaultClearLoop symbol
      (solidityBytesDataWordCount old.toNat - stringFirstClearedWord len.toNat) 0
      (by cases symbol <;> simp [constructorVaultTail]) hperm
      (by rw [UInt256.toNat_ofNat_of_lt hcount]; omega) r2
    refine ⟨_, UInt256.ofNat
      (solidityBytesDataWordCount old.toNat - stringFirstClearedWord len.toNat),
      aw3, k3, C3, .inr rfl, ?_⟩
    simpa only [stringClearedAccounts, if_neg (show ¬ old.toNat < 32 by omega),
      show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, u256_zero_add] using r3

end Benchmarks.Morpho.MetaMorphoV1_1
