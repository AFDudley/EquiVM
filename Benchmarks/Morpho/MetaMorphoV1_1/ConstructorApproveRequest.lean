import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDecimalsOffset
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorApproveABI

/-! Store the final immutable and reserve the initial maximum approval request. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

def constructorApprovalValue : UInt256 := UInt256.lnot ⟨0⟩

def constructorApprovalMemory (mem : ByteArray) (a : ConstructorArgs) (ptr decimals : UInt256) : ByteArray :=
  constructorApproveMemory (writeWord mem 448 (constructorDecimalsOffset decimals))
    ptr a.morpho constructorApprovalValue

theorem constructorApproveRequest {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw ptr decimals : UInt256}
    {σ : AccountMap} {k C : Nat} (a : ConstructorArgs)
    (hmem : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hp : ptr.toNat < 2 ^ 64)
    (hd : decimals.toNat < 256) (hfree : memLoad ⟨64⟩ mem = ptr)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1053⟩
      [⟨255⟩, decimals, UInt256.ofNat a.asset.val, UInt256.ofNat a.morpho.val, ⟨32⟩, ⟨64⟩]
      mem aw rdata σ k C) :
    (¬ allocationFits ptr ⟨100⟩ ∧ RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    (allocationFits ptr ⟨100⟩ ∧ ∃ gasArg aw' k' C',
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1126⟩
        [gasArg, UInt256.ofNat a.asset.val, ⟨0⟩, ptr + ⟨32⟩, ⟨68⟩, ⟨0⟩, ⟨0⟩,
          UInt256.ofNat a.morpho.val, UInt256.ofNat a.asset.val, ptr, ⟨32⟩, ⟨64⟩]
        (constructorApprovalMemory mem a ptr decimals) aw' rdata σ k' C') := by
  have he := constructorDecimalsOffset_word decimals hd
  have hf : memLoad (UInt256.ofNat 64) (writeWord mem 448 (constructorDecimalsOffset decimals)) = ptr :=
    (memLoad_writeWord_disjoint mem 448 ⟨64⟩ _ hmem (.inl (by decide))).trans hfree
  change memLoad ⟨64⟩
    ((constructorDecimalsOffset decimals).toByteArray.write 0 mem 448 32) = ptr at hf
  have h32 := uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)
  change (ptr + ⟨32⟩).toNat = ptr.toNat + 32 at h32
  have h36 := uadd_word_ofNat_toNat ptr 36 (by change _ < 2 ^ 256; omega)
  have h68 := uadd_word_ofNat_toNat ptr 68 (by change _ < 2 ^ 256; omega)
  have hm : metaMorphoV1_1Creation_block_1053_memory (mem := mem) (x1 := decimals)
      (x3 := UInt256.ofNat a.morpho.val) (x4 := ⟨32⟩) (x5 := ⟨64⟩) =
      encodedWordCallMemory (writeWord mem 448 (constructorDecimalsOffset decimals))
        ptr constructorApproveSelectorWord [UInt256.ofNat a.morpho.val, constructorApprovalValue] := by
    simp only [metaMorphoV1_1Creation_block_1053_memory, he,
      show (UInt256.ofNat 448).toNat = 448 from rfl, hf, h32, h36, h68,
      encodedWordCallMemory, wordCallMemory, wordSequenceMemory, Nat.add_assoc]
    rfl
  obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_1053_packed (by simp) (by native_decide) rd
  simp only [metaMorphoV1_1Creation_block_1053_stack, he,
    show (UInt256.ofNat 448).toNat = 448 from rfl, hf, hm] at r1
  change RD _ I g s0 ⟨2608⟩
    [ptr, ⟨100⟩, ⟨1119⟩, ptr + ⟨32⟩, ⟨0⟩, ⟨0⟩, UInt256.ofNat a.morpho.val,
      UInt256.ofNat a.asset.val, ptr, ⟨32⟩, ⟨64⟩]
    (encodedWordCallMemory (writeWord mem 448 (constructorDecimalsOffset decimals))
      ptr constructorApproveSelectorWord [UInt256.ofNat a.morpho.val, constructorApprovalValue])
    _ rdata σ _ _ at r1
  by_cases hfit : allocationFits ptr ⟨100⟩
  · obtain ⟨_, _, _, r2⟩ := constructorAllocateReturn (by simp) hfit (by native_decide) r1
    obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1Creation_block_1119_packed (by simp) r2
    have hl : memLoad ptr (constructorApprovalMemory mem a ptr decimals) = ⟨68⟩ := by
      simpa only [constructorApproveCalldata_size] using
        (constructorApproveMemory_buffer (writeWord mem 448 (constructorDecimalsOffset decimals))
          ptr a.morpho constructorApprovalValue hlo).length
    simp only [metaMorphoV1_1Creation_block_1119_stack] at r3
    change RD _ I g s0 ⟨1126⟩
      [_ , UInt256.ofNat a.asset.val, ⟨0⟩, ptr + ⟨32⟩,
        memLoad ptr (constructorApprovalMemory mem a ptr decimals), ⟨0⟩, ⟨0⟩,
        UInt256.ofNat a.morpho.val, UInt256.ofNat a.asset.val, ptr, ⟨32⟩, ⟨64⟩]
      (constructorApprovalMemory mem a ptr decimals) aw3 rdata σ k3 C3 at r3
    rw [hl] at r3
    exact .inr ⟨hfit, _, aw3, k3, C3, r3⟩
  · exact .inl ⟨hfit, constructorAllocateRevert (by simp) hfit r1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
