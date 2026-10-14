import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultClearDispatch

/-! Compute the first obsolete vault-string word and its clearing count. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

def constructorVaultClearCountPC (symbol : Bool) : UInt256 := if symbol then ⟨1775⟩ else ⟨2032⟩

theorem constructorVaultClearChoose {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {old len ptr : UInt256} (a : ConstructorArgs) (symbol : Bool)
    (hsmall : len.toNat < 2 ^ 255)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultClearStartPC symbol)
      (old :: len :: ptr :: constructorVaultTail a symbol) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorVaultClearCountPC symbol)
      (solidityBytesDataBaseSlot (stringViewSlot symbol) ::
        UInt256.ofNat (stringFirstClearedWord len.toNat) :: old :: len :: ptr ::
        constructorVaultTail a symbol) (stringStorageScratch mem symbol) aw' rdata σ k' C' := by
  by_cases hs : len.toNat < 32
  · have hc : UInt256.lt len ⟨32⟩ ≠ ⟨0⟩ := by rw [ult_one hs]; decide
    simp only [stringFirstClearedWord, if_pos hs]
    cases symbol with
    | false =>
      obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_2010_taken_packed
        (by simp [constructorVaultTail]) hc (by native_decide) rd
      obtain ⟨aw2, k2, C2, r2⟩ := metaMorphoV1_1Creation_block_2073_packed
        (by simp [constructorVaultTail]) (by native_decide) r1
      change RD _ I g s0 ⟨2032⟩
        (keccakWord ⟨0⟩ ⟨32⟩ (writeWord mem 0 ⟨24⟩) :: ⟨0⟩ :: old :: len :: ptr ::
          constructorVaultTail a false) (stringStorageScratch mem false) aw2 rdata σ k2 C2 at r2
      rw [storageSlotScratch_hash] at r2
      exact ⟨aw2, k2, C2, r2⟩
    | true =>
      obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_1753_taken_packed
        (by simp [constructorVaultTail]) hc (by native_decide) rd
      obtain ⟨aw2, k2, C2, r2⟩ := metaMorphoV1_1Creation_block_1816_packed
        (by simp [constructorVaultTail]) (by native_decide) r1
      change RD _ I g s0 ⟨1775⟩
        (keccakWord ⟨0⟩ ⟨32⟩ (writeWord mem 0 ⟨25⟩) :: ⟨0⟩ :: old :: len :: ptr ::
          constructorVaultTail a true) (stringStorageScratch mem true) aw2 rdata σ k2 C2 at r2
      rw [storageSlotScratch_hash] at r2
      exact ⟨aw2, k2, C2, r2⟩
  · have hc : UInt256.lt len ⟨32⟩ = ⟨0⟩ := ult_zero (by change 32 ≤ len.toNat; omega)
    simp only [stringFirstClearedWord, if_neg hs]
    have he : UInt256.shiftRight (len + UInt256.ofNat 31) (UInt256.ofNat 5) =
      UInt256.ofNat (solidityBytesDataWordCount len.toNat) := stringCeilWord len hsmall
    cases symbol with
    | false =>
      obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1Creation_block_2010_fallthrough_packed
        (by simp [constructorVaultTail]) hc rd
      change RD _ I g s0 ⟨2032⟩
        (keccakWord ⟨0⟩ ⟨32⟩ (writeWord mem 0 ⟨24⟩) ::
          UInt256.shiftRight (len + UInt256.ofNat 31) (UInt256.ofNat 5) ::
          old :: len :: ptr :: constructorVaultTail a false)
        (stringStorageScratch mem false) aw1 rdata σ k1 C1 at r1
      rw [storageSlotScratch_hash, he] at r1
      exact ⟨aw1, k1, C1, r1⟩
    | true =>
      obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1Creation_block_1753_fallthrough_packed
        (by simp [constructorVaultTail]) hc rd
      change RD _ I g s0 ⟨1775⟩
        (keccakWord ⟨0⟩ ⟨32⟩ (writeWord mem 0 ⟨25⟩) ::
          UInt256.shiftRight (len + UInt256.ofNat 31) (UInt256.ofNat 5) ::
          old :: len :: ptr :: constructorVaultTail a true)
        (stringStorageScratch mem true) aw1 rdata σ k1 C1 at r1
      rw [storageSlotScratch_hash, he] at r1
      exact ⟨aw1, k1, C1, r1⟩

theorem constructorVaultClearCount {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {old base first : UInt256} {R : List UInt256} (symbol : Bool)
    (hstack : R.length + 5 ≤ 1024)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultClearCountPC symbol)
      (base :: first :: old :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorVaultClearLoopPC symbol)
      (⟨0⟩ :: (base + first) :: UInt256.sub (UInt256.shiftRight (old + ⟨31⟩) ⟨5⟩) first :: R)
      mem aw' rdata σ k' C' := by
  cases symbol with
  | false => exact metaMorphoV1_1Creation_block_2032_packed hstack rd
  | true => exact metaMorphoV1_1Creation_block_1775_packed hstack rd

theorem constructorVaultClearInit {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {old len ptr : UInt256} (a : ConstructorArgs) (symbol : Bool)
    (hold : old.toNat < 2 ^ 255) (hsmall : len.toNat < 2 ^ 255)
    (hshrink : len.toNat ≤ old.toNat)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultClearStartPC symbol)
      (old :: len :: ptr :: constructorVaultTail a symbol) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorVaultClearLoopPC symbol)
      (⟨0⟩ :: (solidityBytesDataBaseSlot (stringViewSlot symbol) +
          UInt256.ofNat (stringFirstClearedWord len.toNat)) ::
        UInt256.ofNat (solidityBytesDataWordCount old.toNat - stringFirstClearedWord len.toNat) ::
        len :: ptr :: constructorVaultTail a symbol)
      (stringStorageScratch mem symbol) aw' rdata σ k' C' := by
  obtain ⟨_, _, _, r1⟩ := constructorVaultClearChoose a symbol hsmall rd
  obtain ⟨aw2, k2, C2, r2⟩ := constructorVaultClearCount symbol
    (by cases symbol <;> simp [constructorVaultTail]) r1
  have hb : solidityBytesDataWordCount old.toNat < UInt256.size := by
    unfold solidityBytesDataWordCount
    change _ < 2 ^ 256
    omega
  have hs : stringFirstClearedWord len.toNat ≤ solidityBytesDataWordCount old.toNat := by
    unfold stringFirstClearedWord solidityBytesDataWordCount
    split <;> omega
  have he : UInt256.sub (UInt256.ofNat (solidityBytesDataWordCount old.toNat))
      (UInt256.ofNat (stringFirstClearedWord len.toNat)) =
      UInt256.ofNat (solidityBytesDataWordCount old.toNat - stringFirstClearedWord len.toNat) := by
    apply u256_inj
    rw [usub_ofNat_lit_toNat hs hb, UInt256.toNat_ofNat_of_lt (by omega)]
  rw [stringCeilWord old hold, he] at r2
  exact ⟨aw2, k2, C2, r2⟩

end Benchmarks.Morpho.MetaMorphoV1_1
