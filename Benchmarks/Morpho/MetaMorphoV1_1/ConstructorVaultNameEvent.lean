import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultEncode
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultEventSource

/-! Emit the initial vault-name event and reach the symbol's storage-header check. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

theorem constructorVaultNameEvent {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (free : Nat) (hperm : I.perm = true)
    (hsmall : a.argumentEnd < 2 ^ 64) (hname : a.nameEnd < 2 ^ 64)
    (hfreeBound : free < 2 ^ 64) (hbelow : a.stringsEnd ≤ free)
    (hn : StringBuffer mem a.argumentEnd a.name) (hv : StringBuffer mem a.nameEnd a.symbol)
    (hfree : memLoad ⟨64⟩ mem = UInt256.ofNat free)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨874⟩
      (UInt256.ofNat a.argumentEnd :: ⟨885⟩ :: stringSetTopic false :: constructorVaultTail a false)
      mem aw rdata σ k C) :
    StringBuffer (stringReturnMemory mem (a.argumentEnd + 32) free (UInt256.ofNat a.name.size))
      a.nameEnd a.symbol ∧
    ByteMemoryPrefix mem
      (stringReturnMemory mem (a.argumentEnd + 32) free (UInt256.ofNat a.name.size)) free ∧
    memLoad ⟨64⟩ (stringReturnMemory mem (a.argumentEnd + 32) free (UInt256.ofNat a.name.size)) =
      UInt256.ofNat free ∧
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨905⟩
      (UInt256.ofNat a.symbol.size :: UInt256.ofNat a.nameEnd :: constructorVaultTail a true)
      (stringReturnMemory mem (a.argumentEnd + 32) free (UInt256.ofNat a.name.size)) aw' rdata σ k' C' := by
  obtain ⟨hns, hvs⟩ := a.string_sizes_small hsmall
  have hnl : (UInt256.ofNat a.name.size).toNat = a.name.size :=
    UInt256.toNat_ofNat_of_lt (by change a.name.size < 2 ^ 256; omega)
  have hvl : (UInt256.ofNat a.symbol.size).toNat = a.symbol.size :=
    UInt256.toNat_ofNat_of_lt (by change a.symbol.size < 2 ^ 256; omega)
  have hnlo : 96 ≤ a.argumentEnd := by unfold ConstructorArgs.argumentEnd; omega
  have hvlo : 96 ≤ a.nameEnd := by unfold ConstructorArgs.nameEnd; omega
  have hnpad : a.name.size ≤ paddedSize a.name.size := by unfold paddedSize; omega
  have hin : a.argumentEnd + 32 + (UInt256.ofNat a.name.size).toNat ≤ mem.size := by
    rw [hnl]; have hb := hn.size; omega
  have hp := stringReturnMemory_bytePrefix mem (a.argumentEnd + 32) free (UInt256.ofNat a.name.size) hin
  have hv' := hv.preserve hp.words hvlo (by change a.nameEnd < 2 ^ 256; omega)
    (by change a.stringsEnd ≤ free; exact hbelow)
  have hff := (stringReturnMemory_free mem (a.argumentEnd + 32) free (UInt256.ofNat a.name.size)
    hin (by have hb := hn.size; omega) (by
      unfold ConstructorArgs.stringsEnd ConstructorArgs.nameEnd at hbelow; omega)).trans hfree
  obtain ⟨_, _, _, r1⟩ := constructorVaultEncode a false a.argumentEnd free hn hns
    (by change a.argumentEnd + 32 < 2 ^ 256; omega)
    (by unfold ConstructorArgs.stringsEnd ConstructorArgs.nameEnd at hbelow; omega)
    (by change free + 64 + paddedSize a.name.size + 32 < 2 ^ 256; unfold paddedSize; omega)
    hfree rd
  obtain ⟨aw2, k2, C2, r2⟩ := metaMorphoV1_1Creation_block_885_fallthrough_packed
    (by simp [constructorVaultTail]) hperm
    (by rw [hv'.length]; apply ugt_zero; rw [hvl]; change a.symbol.size ≤ 2 ^ 64 - 1; omega) r1
  refine ⟨hv', hp, hff, aw2, k2, C2, ?_⟩
  simpa only [metaMorphoV1_1Creation_block_885_fallthrough_stack, hv'.length] using r2

end Benchmarks.Morpho.MetaMorphoV1_1
