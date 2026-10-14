import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStorageClear
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_003
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_004
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_008
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_009

/-! Decode and validate the existing vault-name and vault-symbol storage headers. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

def constructorVaultHeaderPC (symbol : Bool) : UInt256 := if symbol then ⟨905⟩ else ⟨780⟩
def constructorVaultCheckPC (symbol : Bool) : UInt256 := if symbol then ⟨921⟩ else ⟨796⟩
def constructorVaultOldPC (symbol : Bool) : UInt256 := if symbol then ⟨930⟩ else ⟨805⟩
def constructorVaultStorePC (symbol : Bool) : UInt256 := if symbol then ⟨938⟩ else ⟨813⟩
def constructorVaultTail (a : ConstructorArgs) (symbol : Bool) : List UInt256 :=
  (if symbol then [] else [UInt256.ofNat a.nameEnd]) ++
    [UInt256.ofNat a.asset.val, UInt256.ofNat a.morpho.val, ⟨32⟩, ⟨64⟩]

theorem constructorVaultHeader {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (symbol : Bool) (hstack : R.length + 4 ≤ 1024)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultHeaderPC symbol)
      R mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorVaultCheckPC symbol)
      (UInt256.land (solcSlotWord σ I (stringViewSlot symbol)) ⟨1⟩ ::
        storageStringLength (solcSlotWord σ I (stringViewSlot symbol)) :: R)
      mem aw' rdata σ k' C' := by
  have hshift : UInt256.shiftRight (solcSlotWord σ I (stringViewSlot symbol)) (UInt256.ofNat 1) =
      UInt256.div (solcSlotWord σ I (stringViewSlot symbol)) ⟨2⟩ :=
    wordShiftRight_eq_div (solcSlotWord σ I (stringViewSlot symbol)) 1 (by decide)
  by_cases hz : UInt256.land (solcSlotWord σ I (stringViewSlot symbol)) ⟨1⟩ = ⟨0⟩
  · have hc : UInt256.isZero (UInt256.land (solcSlotWord σ I (stringViewSlot symbol)) ⟨1⟩) ≠ ⟨0⟩ := by
      rw [hz]; decide
    cases symbol with
    | false =>
      obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_780_taken_packed
        hstack hc (by native_decide) rd
      obtain ⟨aw2, k2, C2, r2⟩ := metaMorphoV1_1Creation_block_2081_packed
        (by omega) (by native_decide) r1
      refine ⟨aw2, k2, C2, ?_⟩
      change RD _ I g s0 ⟨796⟩ (UInt256.land (solcSlotWord σ I ⟨24⟩) ⟨1⟩ ::
        UInt256.land (UInt256.ofNat 127)
          (UInt256.shiftRight (solcSlotWord σ I ⟨24⟩) (UInt256.ofNat 1)) :: R)
        mem aw2 rdata σ k2 C2 at r2
      change UInt256.shiftRight (solcSlotWord σ I ⟨24⟩) (UInt256.ofNat 1) =
        UInt256.div (solcSlotWord σ I ⟨24⟩) ⟨2⟩ at hshift
      simpa only [hshift, storageStringLength, if_pos hz,
        u256_land_comm (UInt256.ofNat 127)] using r2
    | true =>
      obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_905_taken_packed
        hstack hc (by native_decide) rd
      obtain ⟨aw2, k2, C2, r2⟩ := metaMorphoV1_1Creation_block_1844_packed
        (by omega) (by native_decide) r1
      refine ⟨aw2, k2, C2, ?_⟩
      change RD _ I g s0 ⟨921⟩ (UInt256.land (solcSlotWord σ I ⟨25⟩) ⟨1⟩ ::
        UInt256.land (UInt256.ofNat 127)
          (UInt256.shiftRight (solcSlotWord σ I ⟨25⟩) (UInt256.ofNat 1)) :: R)
        mem aw2 rdata σ k2 C2 at r2
      change UInt256.shiftRight (solcSlotWord σ I ⟨25⟩) (UInt256.ofNat 1) =
        UInt256.div (solcSlotWord σ I ⟨25⟩) ⟨2⟩ at hshift
      simpa only [hshift, storageStringLength, if_pos hz,
        u256_land_comm (UInt256.ofNat 127)] using r2
  · have hc := isZero_eq_zero_of_ne hz
    have hnext : ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
        (constructorVaultCheckPC symbol)
        (UInt256.land (solcSlotWord σ I (stringViewSlot symbol)) ⟨1⟩ ::
          UInt256.shiftRight (solcSlotWord σ I (stringViewSlot symbol)) (UInt256.ofNat 1) :: R)
        mem aw' rdata σ k' C' := by
      cases symbol with
      | false => exact metaMorphoV1_1Creation_block_780_fallthrough_packed hstack hc rd
      | true => exact metaMorphoV1_1Creation_block_905_fallthrough_packed hstack hc rd
    simpa only [storageStringLength, if_neg hz, hshift] using hnext

theorem constructorVaultCheck {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {len ptr : UInt256} (a : ConstructorArgs) (symbol : Bool)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultCheckPC symbol)
      (UInt256.land (solcSlotWord σ I (stringViewSlot symbol)) ⟨1⟩ ::
        storageStringLength (solcSlotWord σ I (stringViewSlot symbol)) ::
        len :: ptr :: constructorVaultTail a symbol) mem aw rdata σ k C) :
    (¬ storageStringValid (solcSlotWord σ I (stringViewSlot symbol)) ∧
      RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    (storageStringValid (solcSlotWord σ I (stringViewSlot symbol)) ∧
      ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
        (constructorVaultOldPC symbol)
        (storageStringLength (solcSlotWord σ I (stringViewSlot symbol)) ::
          len :: ptr :: constructorVaultTail a symbol) mem aw' rdata σ k' C') := by
  by_cases hv : storageStringValid (solcSlotWord σ I (stringViewSlot symbol))
  · refine .inr ⟨hv, ?_⟩
    have hc := u256_eq_of_ne (Ne.symm hv)
    cases symbol with
    | false => exact metaMorphoV1_1Creation_block_796_fallthrough_packed (by simp) hc rd
    | true => exact metaMorphoV1_1Creation_block_921_fallthrough_packed (by simp) hc rd
  · refine .inl ⟨hv, ?_⟩
    have hc : UInt256.eq
        (UInt256.lt (storageStringLength (solcSlotWord σ I (stringViewSlot symbol))) ⟨32⟩)
        (UInt256.land (solcSlotWord σ I (stringViewSlot symbol)) ⟨1⟩) ≠ ⟨0⟩ := by
      rw [(Classical.not_not.mp hv).symm, u256_eq_refl]; decide
    cases symbol with
    | false =>
      have r1 := metaMorphoV1_1Creation_block_796_taken (by simp) hc (by native_decide) rd
      exact metaMorphoV1_1Creation_block_1824 (by simp [metaMorphoV1_1Creation_block_796_taken_stack]) r1
    | true =>
      have r1 := metaMorphoV1_1Creation_block_921_taken (by simp) hc (by native_decide) rd
      exact metaMorphoV1_1Creation_block_1824 (by simp [metaMorphoV1_1Creation_block_921_taken_stack]) r1

end Benchmarks.Morpho.MetaMorphoV1_1
