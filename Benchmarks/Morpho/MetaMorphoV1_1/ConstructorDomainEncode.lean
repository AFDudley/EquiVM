import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDomainMemory
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorAllocation

/-! Build the constructor's domain preimage and reach its checked allocation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

def constructorDomainTail (a : ConstructorArgs) : List UInt256 :=
  [UInt256.ofNat a.owner.val, UInt256.ofNat a.morpho.val, UInt256.ofNat a.argumentEnd,
    UInt256.ofNat a.nameEnd, UInt256.ofNat a.asset.val, a.initialTimelock, ⟨32⟩, ⟨64⟩]

set_option maxRecDepth 2000 in
theorem constructorDomainEncode {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (free : Nat) (hlo : 480 ≤ a.stringsEnd)
    (hptr : a.stringsEnd + 160 < UInt256.size) (hfreeBound : free < 2 ^ 64)
    (hempty : BytesBuffer mem (UInt256.ofNat a.stringsEnd) ByteArray.empty)
    (hversion : BytesBuffer mem (UInt256.ofNat (a.stringsEnd + 96)) "1".toUTF8)
    (hfree : memLoad ⟨64⟩ mem = UInt256.ofNat free)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨479⟩
      (constructorVersionWord :: constructorMetadataTail a a.stringsEnd true)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨2608⟩
      (UInt256.ofNat free :: ⟨192⟩ :: ⟨588⟩ :: UInt256.ofNat free ::
        UInt256.ofNat (free + 32) :: constructorDomainTail a)
      (constructorDomainPreimageMemory mem I free) aw' rdata σ k' C' := by
  have hm : 96 ≤ mem.size := by
    have hsize := hempty.size
    rw [UInt256.toNat_ofNat_of_lt (by omega)] at hsize
    omega
  obtain ⟨hn, hv⟩ := constructorDomainLiteralHashes mem a.stringsEnd hlo hptr hempty hversion
  have hf := (constructorDomainConstantsMemory_free mem hm).trans hfree
  simp only [constructorDomainConstantsMemory, constructorNameHashMemory,
    constructorVersionImmutableMemory, Reasoning.Theory.writeWord,
    show UInt256.ofNat 32 = ⟨32⟩ from rfl] at hn hv hf
  have hfit (n : Nat) (hn : n ≤ 192) : free + n < UInt256.size := by
    change free + n < 2 ^ 256
    omega
  have hadd (n : Nat) (hn : n ≤ 192) :
      (UInt256.ofNat free + UInt256.ofNat n).toNat = free + n := by
    rw [ofNat_add_words, UInt256.toNat_ofNat_of_lt (hfit n hn)]
  have hmem : metaMorphoV1_1Creation_block_479_memory (ee := I) (mem := mem)
      (x0 := constructorVersionWord) (x1 := UInt256.ofNat a.stringsEnd)
      (x2 := UInt256.ofNat (a.stringsEnd + 96)) (x9 := ⟨32⟩) (x10 := ⟨64⟩) =
      constructorDomainPreimageMemory mem I free := by
    simp only [metaMorphoV1_1Creation_block_479_memory,
      show (UInt256.ofNat 384).toNat = 384 from rfl,
      show (UInt256.ofNat 288).toNat = 288 from rfl,
      show (UInt256.ofNat 320).toNat = 320 from rfl,
      show (UInt256.ofNat 224).toNat = 224 from rfl, hn, hv, hf]
    simp only [show (⟨32⟩ : UInt256) = UInt256.ofNat 32 from rfl,
      show (⟨64⟩ : UInt256) = UInt256.ofNat 64 from rfl,
      hadd 32 (by omega), hadd 64 (by omega), hadd 96 (by omega), hadd 128 (by omega),
      hadd 160 (by omega), UInt256.toNat_ofNat_of_lt (show free < UInt256.size by
        have := hfit 0 (by omega); omega)]
    simp only [constructorDomainPreimageMemory, constructorDomainConstantsMemory,
      constructorNameHashMemory, constructorVersionImmutableMemory, constructorDomainWords,
      wordSequenceMemory, domainTypeHash, Reasoning.Theory.writeWord, Nat.add_assoc]
    rfl
  obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1Creation_block_479_packed
    (by simp) (by native_decide) rd
  refine ⟨aw1, k1, C1, ?_⟩
  simp only [metaMorphoV1_1Creation_block_479_stack,
    show (UInt256.ofNat 384).toNat = 384 from rfl,
    show (UInt256.ofNat 288).toNat = 288 from rfl,
    show (UInt256.ofNat 320).toNat = 320 from rfl,
    show (UInt256.ofNat 224).toNat = 224 from rfl, hn, hv, hf, hmem] at r1
  simpa only [show (⟨32⟩ : UInt256) = UInt256.ofNat 32 from rfl,
    ofNat_add_words, constructorDomainTail] using r1

end Benchmarks.Morpho.MetaMorphoV1_1
