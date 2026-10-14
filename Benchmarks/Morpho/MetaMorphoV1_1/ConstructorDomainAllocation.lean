import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDomainEncode

/-! The checked allocation and final byte buffer of the constructor domain preimage. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

def constructorDomainAllocatedMemory (mem : ByteArray) (I : ExecutionEnv) (free : Nat) : ByteArray :=
  packedWordsMemory (constructorDomainConstantsMemory mem) free (constructorDomainWords I)

theorem constructorDomainAllocatedMemory_eq (mem : ByteArray) (I : ExecutionEnv) (free : Nat) :
    writeWord (constructorDomainPreimageMemory mem I free) 64
      (nextCursor (UInt256.ofNat free) ⟨192⟩) = constructorDomainAllocatedMemory mem I free := by
  have hn : nextCursor (UInt256.ofNat free) ⟨192⟩ = UInt256.ofNat (free + 192) :=
    ofNat_add_words free 192
  rw [hn]
  simp only [constructorDomainAllocatedMemory, constructorDomainPreimageMemory,
    packedWordsMemory, constructorDomainWords, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc]
  rfl

theorem constructorDomainAllocatedMemory_buffer (mem : ByteArray) (I : ExecutionEnv) (free : Nat)
    (hlo : 96 ≤ free) (hfit : free < UInt256.size) :
    BytesBuffer (constructorDomainAllocatedMemory mem I free) (UInt256.ofNat free)
      (wordBytes (constructorDomainWords I)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [UInt256.toNat_ofNat_of_lt hfit, wordBytes_size]
    exact packedWordsMemory_size _ _ _ (by simp [constructorDomainWords])
  · rw [wordBytes_size]
    exact packedWordsMemory_length _ _ _ hlo hfit
  · rw [UInt256.toNat_ofNat_of_lt hfit, wordBytes_size]
    exact packedWordsMemory_read _ _ _ hlo (by simp [constructorDomainWords])

theorem constructorDomainAllocatedMemory_free (mem : ByteArray) (I : ExecutionEnv) (free : Nat) :
    memLoad ⟨64⟩ (constructorDomainAllocatedMemory mem I free) = UInt256.ofNat (free + 192) := by
  simpa only [constructorDomainWords, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc] using
    packedWordsMemory_free (constructorDomainConstantsMemory mem) free (constructorDomainWords I)

theorem constructorDomainAllocatedMemory_hash (mem : ByteArray) (I : ExecutionEnv) (free : Nat)
    (hlo : 96 ≤ free) (hfit : free < 2 ^ 64) :
    keccakWord (UInt256.ofNat (free + 32))
      (memLoad (UInt256.ofNat free) (constructorDomainAllocatedMemory mem I free))
      (constructorDomainAllocatedMemory mem I free) = constructorDomainHash I := by
  have hf : free < UInt256.size := by change free < 2 ^ 256; omega
  have hh := (constructorDomainAllocatedMemory_buffer mem I free hlo hf).keccak
    (by rw [UInt256.toNat_ofNat_of_lt hf]; change free + 32 < 2 ^ 256; omega)
    (by rw [wordBytes_size]; simp [constructorDomainWords]; decide)
  simpa only [ofNat_add_words, constructorDomainHash] using hh

theorem constructorDomainAllocation {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (free : Nat) (hlo : 480 ≤ a.stringsEnd)
    (hptr : a.stringsEnd + 160 < UInt256.size) (hfreeBound : free < 2 ^ 64)
    (hempty : BytesBuffer mem (UInt256.ofNat a.stringsEnd) ByteArray.empty)
    (hversion : BytesBuffer mem (UInt256.ofNat (a.stringsEnd + 96)) "1".toUTF8)
    (hfree : memLoad ⟨64⟩ mem = UInt256.ofNat free)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨479⟩
      (constructorVersionWord :: constructorMetadataTail a a.stringsEnd true)
      mem aw rdata σ k C) :
    (¬ allocationFits (UInt256.ofNat free) ⟨192⟩ ∧
      RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    (allocationFits (UInt256.ofNat free) ⟨192⟩ ∧ ∃ aw' k' C',
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨588⟩
        (UInt256.ofNat free :: UInt256.ofNat (free + 32) :: constructorDomainTail a)
        (constructorDomainAllocatedMemory mem I free) aw' rdata σ k' C') := by
  obtain ⟨_, _, _, r1⟩ := constructorDomainEncode a free hlo hptr hfreeBound hempty hversion hfree rd
  by_cases hfit : allocationFits (UInt256.ofNat free) ⟨192⟩
  · right
    refine ⟨hfit, ?_⟩
    obtain ⟨aw2, k2, C2, r2⟩ := constructorAllocateReturn
      (by simp [constructorDomainTail]) hfit (by native_decide) r1
    exact ⟨aw2, k2, C2, by simpa only [constructorDomainAllocatedMemory_eq] using r2⟩
  · exact .inl ⟨hfit, constructorAllocateRevert (by simp [constructorDomainTail]) hfit r1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
