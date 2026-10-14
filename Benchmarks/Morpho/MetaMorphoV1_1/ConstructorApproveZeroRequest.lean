import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorApproveABI
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_006
import Benchmarks.Morpho.MetaMorphoV1_1.WordCallBytePrefix

/-! Allocate the fallback zero approval while retaining the original maximum request. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

theorem constructorApproveMemory_bytePrefix (mem : ByteArray) (ptr : UInt256)
    (spender : AccountAddress) (value : UInt256) :
    ByteMemoryPrefix mem (constructorApproveMemory mem ptr spender value) ptr.toNat :=
  allocatedWordCallMemory_bytePrefix mem ptr constructorApproveSelectorWord _

theorem constructorApproveZeroRequest {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw ptr request : UInt256}
    {σ : AccountMap} {k C : Nat} (asset spender : AccountAddress)
    (hp : ptr.toNat < 2 ^ 64) (hfree : memLoad ⟨64⟩ mem = ptr)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1420⟩
      [UInt256.ofNat spender.val, UInt256.ofNat asset.val, request, ⟨32⟩, ⟨64⟩]
      mem aw rdata σ k C) :
    (¬ allocationFits ptr ⟨100⟩ ∧ RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    (allocationFits ptr ⟨100⟩ ∧ ∃ aw' k' C',
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨3692⟩
        [UInt256.ofNat asset.val, ptr, ⟨1475⟩, UInt256.ofNat asset.val, request, ⟨1480⟩, ⟨64⟩]
        (constructorApproveMemory mem ptr spender ⟨0⟩) aw' rdata σ k' C') := by
  have h32 : (ptr + (⟨32⟩ : UInt256)).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)
  have h36 := uadd_word_ofNat_toNat ptr 36 (by change _ < 2 ^ 256; omega)
  have h68 := uadd_word_ofNat_toNat ptr 68 (by change _ < 2 ^ 256; omega)
  have hm : metaMorphoV1_1Creation_block_1420_memory (mem := mem)
      (x0 := UInt256.ofNat spender.val) (x3 := ⟨32⟩) (x4 := ⟨64⟩) =
      encodedWordCallMemory mem ptr constructorApproveSelectorWord [UInt256.ofNat spender.val, ⟨0⟩] := by
    simp only [metaMorphoV1_1Creation_block_1420_memory, hfree, h32, h36, h68,
      encodedWordCallMemory, wordCallMemory, wordSequenceMemory, Nat.add_assoc]
    rfl
  obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_1420_packed (by simp) (by native_decide) rd
  simp only [metaMorphoV1_1Creation_block_1420_stack, hfree, hm] at r1
  by_cases hfit : allocationFits ptr ⟨100⟩
  · obtain ⟨_, _, _, r2⟩ := constructorAllocateReturn (by simp) hfit (by native_decide) r1
    obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1Creation_block_1469_packed
      (by simp) (by native_decide) r2
    exact .inr ⟨hfit, aw3, k3, C3, r3⟩
  · exact .inl ⟨hfit, constructorAllocateRevert (by simp) hfit r1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
