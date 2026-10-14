import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStorageMemory
import Benchmarks.Morpho.MetaMorphoV1_1.SelectorCallMemory
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_016

/-! The allocated selector-only request for the constructor's optional decimals query. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

def constructorDecimalsSelectorWord : UInt256 := UInt256.shiftLeft (UInt256.ofNat 826074471) ⟨224⟩

theorem constructorDecimalsEncode : config.externalABI.encode? "decimals" [] =
    some (constructorDecimalsSelectorWord.toByteArray.extract 0 4) := by
  change encodeCallWithSelector?
    (ByteArray.mk ((EVM.Word.ofNat 0x313ce567).toBytesBE.drop 28).toArray) [] [] = _
  simp only [encodeCallWithSelector?, encodeABIValues?, encodeABIValuesFrom?,
    abiTupleHeadSize?, bind, Option.bind]
  decide +kernel

theorem constructorDecimalsEntry {tail : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (ptr : Nat)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨434⟩
      (constructorMetadataTail a ptr true) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨3545⟩
      (UInt256.ofNat a.asset.val :: ⟨443⟩ :: constructorMetadataTail a ptr true)
      mem aw' rdata σ k' C' :=
  metaMorphoV1_1Creation_block_434_packed (by simp) (by native_decide) rd

theorem constructorDecimalsRequest {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr : UInt256} {R : List UInt256} (asset : AccountAddress)
    (hstack : R.length + 12 ≤ 1024) (hlo : 96 ≤ ptr.toNat) (hptr : ptr.toNat < 2 ^ 64)
    (hfree : memLoad ⟨64⟩ mem = ptr)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨3545⟩
      (UInt256.ofNat asset.val :: R) mem aw rdata σ k C) :
    (¬ allocationFits ptr ⟨36⟩ ∧ RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    (allocationFits ptr ⟨36⟩ ∧ ∃ gasArg aw' k' C',
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨3594⟩
        (gasArg :: UInt256.ofNat asset.val :: (ptr + ⟨32⟩) :: ⟨4⟩ :: ⟨0⟩ :: ⟨0⟩ :: R)
        (allocatedWordCallMemory mem ptr constructorDecimalsSelectorWord []) aw' rdata σ k' C') := by
  change memLoad (UInt256.ofNat 64) mem = ptr at hfree
  have hp : (ptr + UInt256.ofNat 32).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)
  obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_3545_packed (by omega) (by native_decide) rd
  simp only [metaMorphoV1_1Creation_block_3545_stack,
    metaMorphoV1_1Creation_block_3545_memory, hfree, hp] at r1
  change RD _ I g s0 ⟨2608⟩
    (ptr :: ⟨36⟩ :: ⟨3581⟩ :: ptr :: (ptr + ⟨32⟩) :: UInt256.ofNat asset.val :: ⟨0⟩ :: ⟨0⟩ :: R)
    (encodedWordCallMemory mem ptr constructorDecimalsSelectorWord []) _ rdata σ _ _ at r1
  by_cases hf : allocationFits ptr ⟨36⟩
  · obtain ⟨_, _, _, r2⟩ := constructorAllocateReturn
      (by simp only [List.length_cons]; omega) hf (by native_decide) r1
    obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1Creation_block_3581_packed
      (by simp only [List.length_cons]; omega) r2
    have hl : memLoad ptr (allocatedWordCallMemory mem ptr constructorDecimalsSelectorWord []) = ⟨4⟩ := by
      simpa only [ByteArray.size_extract, toByteArray_size] using
        (allocatedSelectorCall_buffer mem ptr constructorDecimalsSelectorWord hlo).length
    have ha : UInt256.land
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
        (UInt256.ofNat asset.val) = UInt256.ofNat asset.val := by
      rw [u256_land_comm]
      exact addressWord_val_clean asset
    simp only [metaMorphoV1_1Creation_block_3581_stack] at r3
    change RD _ I g s0 ⟨3594⟩
      (_ :: _ :: (ptr + ⟨32⟩) :: memLoad ptr (allocatedWordCallMemory mem ptr constructorDecimalsSelectorWord []) ::
        ⟨0⟩ :: ⟨0⟩ :: R) (allocatedWordCallMemory mem ptr constructorDecimalsSelectorWord [])
      aw3 rdata σ k3 C3 at r3
    rw [hl, ha] at r3
    exact .inr ⟨hf, _, aw3, k3, C3, r3⟩
  · exact .inl ⟨hf, constructorAllocateRevert (by simp only [List.length_cons]; omega) hf r1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
