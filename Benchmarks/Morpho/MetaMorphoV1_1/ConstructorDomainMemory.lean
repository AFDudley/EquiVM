import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDomainSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDomainLiteralMemory
import Benchmarks.Morpho.MetaMorphoV1_1.DomainMemory

/-! Immutable stores and the allocated EIP-712 constructor preimage. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

-- LIBRARY CANDIDATE: the word-store form of the disjoint MLOAD theorem.
theorem memLoad_writeWord_disjoint (mem : ByteArray) (off : Nat) (ptr word : UInt256)
    (hin : ptr.toNat + 32 ≤ mem.size)
    (hdis : ptr.toNat + 32 ≤ off ∨ off + 32 ≤ ptr.toNat) :
    memLoad ptr (writeWord mem off word) = memLoad ptr mem :=
  memLoad_write_disjoint mem off ptr word hin hdis

-- LIBRARY CANDIDATE: hash the payload of a length-prefixed byte buffer.
theorem SourceMemory.BytesBuffer.keccak {mem bytes : ByteArray} {ptr : UInt256}
    (buffer : BytesBuffer mem ptr bytes) (hptr : ptr.toNat + 32 < UInt256.size)
    (hsize : bytes.size < UInt256.size) :
    keccakWord (ptr + UInt256.ofNat 32) (memLoad ptr mem) mem =
      uInt256OfByteArray (KEC bytes) := by
  have hadd : (ptr + UInt256.ofNat 32).toNat = ptr.toNat + 32 := by
    nth_rw 1 [← u256_ofNat_toNat ptr]
    rw [ofNat_add_words, UInt256.toNat_ofNat_of_lt hptr]
  rw [buffer.length, keccakWord, hadd, UInt256.toNat_ofNat_of_lt hsize, buffer.data,
    uInt256OfByteArray_eq]

def constructorVersionImmutableMemory (mem : ByteArray) : ByteArray :=
  writeWord mem 384 constructorVersionWord

def constructorNameHashMemory (mem : ByteArray) : ByteArray :=
  writeWord (constructorVersionImmutableMemory mem) 288 constructorNameHash

def constructorDomainConstantsMemory (mem : ByteArray) : ByteArray :=
  writeWord (writeWord (constructorNameHashMemory mem) 320 constructorVersionHash)
    224 (UInt256.ofNat Ethereum.chainId)

def constructorDomainWords (I : ExecutionEnv) : List UInt256 :=
  [domainTypeHash, constructorNameHash, constructorVersionHash,
    UInt256.ofNat Ethereum.chainId, UInt256.ofNat I.codeOwner.val]

def constructorDomainHash (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (KEC (wordBytes (constructorDomainWords I)))

def constructorDomainPreimageMemory (mem : ByteArray) (I : ExecutionEnv) (free : Nat) : ByteArray :=
  writeWord (wordSequenceMemory (constructorDomainConstantsMemory mem) (free + 32)
    (constructorDomainWords I)) free ⟨160⟩

theorem constructorDomainConstantsMemory_free (mem : ByteArray) (hmem : 96 ≤ mem.size) :
    memLoad ⟨64⟩ (constructorDomainConstantsMemory mem) = memLoad ⟨64⟩ mem := by
  unfold constructorDomainConstantsMemory constructorNameHashMemory constructorVersionImmutableMemory
  rw [memLoad_writeWord_disjoint _ 224 ⟨64⟩ _
      (by simp only [writeWord_sparse_size]; change 96 ≤ _; omega) (.inl (by decide)),
    memLoad_writeWord_disjoint _ 320 ⟨64⟩ _
      (by simp only [writeWord_sparse_size]; change 96 ≤ _; omega) (.inl (by decide)),
    memLoad_writeWord_disjoint _ 288 ⟨64⟩ _
      (by rw [writeWord_sparse_size]; change 96 ≤ _; omega) (.inl (by decide)),
    memLoad_writeWord_disjoint mem 384 ⟨64⟩ _ hmem (.inl (by decide))]

theorem constructorDomainLiteralHashes (mem : ByteArray) (ptr : Nat)
    (hlo : 480 ≤ ptr) (hptr : ptr + 160 < UInt256.size)
    (hempty : BytesBuffer mem (UInt256.ofNat ptr) ByteArray.empty)
    (hversion : BytesBuffer mem (UInt256.ofNat (ptr + 96)) "1".toUTF8) :
    keccakWord (UInt256.ofNat ptr + UInt256.ofNat 32)
        (memLoad (UInt256.ofNat ptr) (constructorVersionImmutableMemory mem))
        (constructorVersionImmutableMemory mem) = constructorNameHash ∧
    keccakWord (UInt256.ofNat (ptr + 96) + UInt256.ofNat 32)
        (memLoad (UInt256.ofNat (ptr + 96)) (constructorNameHashMemory mem))
        (constructorNameHashMemory mem) = constructorVersionHash := by
  have hp : (UInt256.ofNat ptr).toNat = ptr := UInt256.toNat_ofNat_of_lt (by omega)
  have hv : (UInt256.ofNat (ptr + 96)).toNat = ptr + 96 := UInt256.toNat_ofNat_of_lt (by omega)
  constructor
  · exact (hempty.writeWord 384 constructorVersionWord (.inr (by rw [hp]; omega))).keccak
      (by rw [hp]; omega) (by decide)
  · exact ((hversion.writeWord 384 constructorVersionWord (.inr (by rw [hv]; omega))).writeWord
      288 constructorNameHash (.inr (by rw [hv]; omega))).keccak
      (by rw [hv]; omega) (by decide)

end Benchmarks.Morpho.MetaMorphoV1_1
