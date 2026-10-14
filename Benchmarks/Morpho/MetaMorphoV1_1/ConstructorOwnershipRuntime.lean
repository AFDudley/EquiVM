import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDomainCache
import Benchmarks.Morpho.MetaMorphoV1_1.Ownership

/-! Constructor ownership stores, event, and the zero-Morpho guard. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

def constructorTimelockTail (a : ConstructorArgs) (ptr : UInt256) : List UInt256 :=
  [a.initialTimelock, ptr, UInt256.ofNat a.argumentEnd, UInt256.ofNat a.nameEnd,
    UInt256.ofNat a.asset.val, UInt256.ofNat a.morpho.val, ⟨32⟩, ⟨64⟩]

theorem constructorOwnershipAccounts (I : ExecutionEnv) (σ : AccountMap) (owner : AccountAddress) :
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σ ⟨9⟩
        (UInt256.land (UInt256.lnot solcAddrMask) (codeOwnerStorageWord I σ ⟨9⟩))) ⟨8⟩
      (UInt256.lor (UInt256.ofNat owner.val)
        (UInt256.land (codeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σ ⟨9⟩
            (UInt256.land (UInt256.lnot solcAddrMask) (codeOwnerStorageWord I σ ⟨9⟩))) ⟨8⟩)
          (UInt256.lnot solcAddrMask))) = ownershipAccounts I σ (UInt256.ofNat owner.val) := by
  have hclear : UInt256.land (UInt256.lnot solcAddrMask) (codeOwnerStorageWord I σ ⟨9⟩) =
      setAddressOffset0Word (codeOwnerStorageWord I σ ⟨9⟩) ⟨0⟩ := by
    rw [setAddressOffset0Word_zero, u256_land_comm]
  have hset (old : UInt256) : UInt256.lor (UInt256.ofNat owner.val)
      (UInt256.land old (UInt256.lnot solcAddrMask)) =
      setAddressOffset0Word old (UInt256.ofNat owner.val) := by
    rw [u256_land_comm old (UInt256.lnot solcAddrMask)]
    have hclean : UInt256.land (UInt256.ofNat owner.val) solcAddrMask = UInt256.ofNat owner.val :=
      addressWord_val_clean owner
    simpa only [hclean] using setAddressOffset0Word_bytecode old
      (UInt256.ofNat owner.val)
  rw [hclear, hset]
  rfl

theorem constructorOwnershipRuntime {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (ptr : UInt256) (hperm : I.perm = true)
    (hfree : memLoad ⟨64⟩ mem = ptr)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨616⟩ (constructorOwnershipTail a)
      mem aw rdata σ k C) :
    (a.morpho = ⟨0, by decide⟩ ∧ RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    (a.morpho ≠ ⟨0, by decide⟩ ∧ ∃ aw' k' C',
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨711⟩ (constructorTimelockTail a ptr)
        mem aw' rdata (ownershipAccounts I σ (UInt256.ofNat a.owner.val)) k' C') := by
  have hmask : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (UInt256.ofNat a.morpho.val) = UInt256.ofNat a.morpho.val :=
    solcAddrMask_clean_left (addressWord_val_canonical a.morpho)
  by_cases hz : a.morpho = ⟨0, by decide⟩
  · left
    refine ⟨hz, ?_⟩
    obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_616_taken_packed (by simp) hperm
      (by rw [hmask, (addressWord_eq_zero_iff a.morpho).mpr hz]; decide) (by native_decide) rd
    exact metaMorphoV1_1Creation_block_2142
      (by simp [metaMorphoV1_1Creation_block_616_taken_stack]) r1
  · right
    refine ⟨hz, ?_⟩
    obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1Creation_block_616_fallthrough_packed (by simp) hperm
      (by rw [hmask]; exact isZero_eq_zero_of_ne (fun h ↦ hz ((addressWord_eq_zero_iff a.morpho).mp h))) rd
    refine ⟨aw1, k1, C1, ?_⟩
    simp only [metaMorphoV1_1Creation_block_616_fallthrough_stack, hmask, hfree] at r1
    change RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨711⟩ (constructorTimelockTail a ptr)
      mem aw1 rdata (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨9⟩
          (UInt256.land (UInt256.lnot solcAddrMask) (codeOwnerStorageWord I σ ⟨9⟩))) ⟨8⟩
        (UInt256.lor (UInt256.ofNat a.owner.val)
          (UInt256.land (codeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σ ⟨9⟩
              (UInt256.land (UInt256.lnot solcAddrMask) (codeOwnerStorageWord I σ ⟨9⟩))) ⟨8⟩)
            (UInt256.lnot solcAddrMask)))) k1 C1 at r1
    rwa [constructorOwnershipAccounts] at r1

end Benchmarks.Morpho.MetaMorphoV1_1
