import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDomainAllocation

/-! Cache the domain hash and contract address, then reject a zero initial owner. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

def constructorDomainCachedMemory (mem : ByteArray) (I : ExecutionEnv) (free : Nat) : ByteArray :=
  writeWord (writeWord (constructorDomainAllocatedMemory mem I free) 192 (constructorDomainHash I))
    256 (UInt256.ofNat I.codeOwner.val)

def constructorOwnershipTail (a : ConstructorArgs) : List UInt256 :=
  [UInt256.ofNat a.morpho.val, UInt256.ofNat a.owner.val, UInt256.ofNat a.argumentEnd,
    UInt256.ofNat a.nameEnd, UInt256.ofNat a.asset.val, a.initialTimelock, ⟨32⟩, ⟨64⟩]

-- LIBRARY CANDIDATE: canonical address words are zero exactly for the zero address.
theorem addressWord_eq_zero_iff (address : AccountAddress) :
    UInt256.ofNat address.val = ⟨0⟩ ↔ address = ⟨0, by decide⟩ := by
  constructor
  · intro h
    apply Fin.ext
    have hn := congrArg UInt256.toNat h
    rwa [UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le address.isLt (by decide))] at hn
  · rintro rfl
    rfl

theorem constructorDomainCache {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (free : Nat) (hlo : 96 ≤ free) (hfree : free < 2 ^ 64)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨588⟩
      (UInt256.ofNat free :: UInt256.ofNat (free + 32) :: constructorDomainTail a)
      (constructorDomainAllocatedMemory mem I free) aw rdata σ k C) :
    (a.owner = ⟨0, by decide⟩ ∧ RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    (a.owner ≠ ⟨0, by decide⟩ ∧ ∃ aw' k' C',
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨616⟩ (constructorOwnershipTail a)
        (constructorDomainCachedMemory mem I free) aw' rdata σ k' C') := by
  have hmask : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (UInt256.ofNat a.owner.val) = UInt256.ofNat a.owner.val :=
    solcAddrMask_clean_left (addressWord_val_canonical a.owner)
  by_cases hz : a.owner = ⟨0, by decide⟩
  · left
    refine ⟨hz, ?_⟩
    have h1 := metaMorphoV1_1Creation_block_588_taken (by simp)
      (by rw [hmask, (addressWord_eq_zero_iff a.owner).mpr hz]; decide) (by native_decide) rd
    exact metaMorphoV1_1Creation_block_2157 (by simp [metaMorphoV1_1Creation_block_588_taken_stack]) h1
  · right
    refine ⟨hz, ?_⟩
    obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1Creation_block_588_fallthrough_packed (by simp)
      (by rw [hmask]; exact isZero_eq_zero_of_ne (fun h ↦ hz ((addressWord_eq_zero_iff a.owner).mp h))) rd
    refine ⟨aw1, k1, C1, ?_⟩
    simpa only [metaMorphoV1_1Creation_block_588_fallthrough_stack,
      metaMorphoV1_1Creation_block_588_fallthrough_memory, hmask,
      constructorDomainAllocatedMemory_hash mem I free hlo hfree,
      constructorDomainCachedMemory, constructorOwnershipTail, Reasoning.Theory.writeWord] using h1

end Benchmarks.Morpho.MetaMorphoV1_1
