import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDecodedBuffers
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStringDecode

/-! Both string decodes, retaining their buffers for the constructor body. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

namespace ConstructorArgs

theorem nameAllocationFits (a : ConstructorArgs) (hsmall : a.argumentEnd < 2 ^ 64) :
    allocationFits (UInt256.ofNat a.argumentEnd) (UInt256.ofNat (32 + paddedSize a.name.size)) ↔
      a.nameEnd < 2 ^ 64 :=
  SourceMemory.stringAllocationFits _ _ (by change a.argumentEnd < 2 ^ 256; omega)
    (a.string_sizes_small hsmall).1

theorem symbolAllocationFits (a : ConstructorArgs) (hsmall : a.argumentEnd < 2 ^ 64)
    (hname : a.nameEnd < 2 ^ 64) :
    allocationFits (UInt256.ofNat a.nameEnd) (UInt256.ofNat (32 + paddedSize a.symbol.size)) ↔
      a.stringsEnd < 2 ^ 64 :=
  SourceMemory.stringAllocationFits _ _ (by change a.nameEnd < 2 ^ 256; omega)
    (a.string_sizes_small hsmall).2

end ConstructorArgs

theorem constructorNameRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} (a : ConstructorArgs)
    (hsmall : a.argumentEnd < 2 ^ 64) (hname : ¬ a.nameEnd < 2 ^ 64)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨2690⟩
      [⟨672⟩, UInt256.ofNat a.argumentEnd, ⟨118⟩, ⟨480⟩, UInt256.ofNat a.argumentEnd,
        UInt256.ofNat a.owner.val, a.initialTimelock, UInt256.ofNat a.morpho.val,
        UInt256.ofNat a.asset.val] (constructorArgumentMemory a) aw rdata σ k C) :
    RDrev (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) g s0 := by
  exact constructorStringAllocationRevert 672 a.argumentEnd a.name.size (by simp)
    (a.string_sizes_small hsmall).1
    (by unfold ConstructorArgs.argumentEnd; rw [a.encoded_length]; omega)
    (by omega) (constructorArgumentMemory_name a).length (constructorArgumentMemory_free a)
    (fun h => hname ((a.nameAllocationFits hsmall).mp h)) rd

theorem constructorDecodeName {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} (a : ConstructorArgs)
    (hsmall : a.argumentEnd < 2 ^ 64) (hname : a.nameEnd < 2 ^ 64)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨2690⟩
      [⟨672⟩, UInt256.ofNat a.argumentEnd, ⟨118⟩, ⟨480⟩, UInt256.ofNat a.argumentEnd,
        UInt256.ofNat a.owner.val, a.initialTimelock, UInt256.ofNat a.morpho.val,
        UInt256.ofNat a.asset.val] (constructorArgumentMemory a) aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨2690⟩
      [UInt256.ofNat (704 + paddedSize a.name.size), UInt256.ofNat a.argumentEnd, ⟨150⟩,
        UInt256.ofNat a.argumentEnd, UInt256.ofNat a.owner.val, a.initialTimelock,
        UInt256.ofNat a.morpho.val, UInt256.ofNat a.asset.val]
      (constructorNameMemory a) aw' rdata σ k' C' := by
  have hn := (a.string_sizes_small hsmall).1
  have hptr : a.argumentEnd < UInt256.size := by change _ < 2 ^ 256; omega
  obtain ⟨aw1, k1, C1, r1⟩ := constructorStringReturn (ptr := UInt256.ofNat a.argumentEnd)
    672 a.argumentEnd a.name.size (by simp)
    hn (by have h := (constructorArgumentMemory_name a).size
           rwa [constructorArgumentMemory_size] at h)
    (by omega) (constructorArgumentMemory_name a).length (constructorArgumentMemory_free a)
    ((a.nameAllocationFits hsmall).mpr hname) (by native_decide) rd
  rw [stringAllocationCursor _ _ hn, UInt256.toNat_ofNat_of_lt hptr] at r1
  change RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨118⟩
    [UInt256.ofNat a.argumentEnd, ⟨480⟩, UInt256.ofNat a.argumentEnd,
      UInt256.ofNat a.owner.val, a.initialTimelock, UInt256.ofNat a.morpho.val,
      UInt256.ofNat a.asset.val] (constructorNameMemory a) aw1 rdata σ k1 C1 at r1
  have ho : memLoad ⟨640⟩ (constructorNameMemory a) =
      UInt256.ofNat (224 + paddedSize a.name.size) := by
    have hp := (constructorNameMemory_prefix a hsmall).words.load_preserved
      (off := 640) (by decide)
      (by unfold ConstructorArgs.argumentEnd; rw [a.encoded_length]; omega)
      (by rw [constructorArgumentMemory_size, a.encoded_length]; omega) (by decide)
    exact hp.trans (constructorArgumentMemory_headWord a ⟨5, by decide⟩)
  have ho' : memLoad ((⟨480⟩ : UInt256) + UInt256.ofNat 160) (constructorNameMemory a) =
      UInt256.ofNat (224 + paddedSize a.name.size) := ho
  have hoff : 224 + paddedSize a.name.size < 2 ^ 64 := by
    rw [ConstructorArgs.argumentEnd, a.encoded_length] at hsmall; omega
  have r2 := metaMorphoV1_1Creation_block_118_fallthrough (by simp)
    (by rw [ho']; apply ugt_zero
        change (UInt256.ofNat (224 + paddedSize a.name.size)).toNat ≤ 2 ^ 64 - 1
        rw [UInt256.toNat_ofNat_of_lt (by change _ < 2 ^ 256; omega)]; omega) r1
  simp only [metaMorphoV1_1Creation_block_118_fallthrough_stack, ho'] at r2
  obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1Creation_block_141_packed
    (by simp) (by native_decide) r2
  have hadd : (⟨480⟩ : UInt256) + UInt256.ofNat (224 + paddedSize a.name.size) =
      UInt256.ofNat (704 + paddedSize a.name.size) := by
    change UInt256.ofNat 480 + UInt256.ofNat _ = _
    rw [ofNat_add_words]; congr 1; omega
  exact ⟨aw3, k3, C3, by
    simpa only [metaMorphoV1_1Creation_block_141_stack, hadd] using r3⟩

theorem constructorSymbolRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} (a : ConstructorArgs)
    (hbound : 23666 + a.encoded.length < UInt256.size)
    (hsmall : a.argumentEnd < 2 ^ 64) (hname : a.nameEnd < 2 ^ 64)
    (hsymbol : ¬ a.stringsEnd < 2 ^ 64)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨2690⟩
      [UInt256.ofNat (704 + paddedSize a.name.size), UInt256.ofNat a.argumentEnd, ⟨150⟩,
        UInt256.ofNat a.argumentEnd, UInt256.ofNat a.owner.val, a.initialTimelock,
        UInt256.ofNat a.morpho.val, UInt256.ofNat a.asset.val]
      (constructorNameMemory a) aw rdata σ k C) :
    RDrev (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) g s0 := by
  exact constructorStringAllocationRevert (704 + paddedSize a.name.size)
    a.argumentEnd a.symbol.size (by simp) (a.string_sizes_small hsmall).2
    (by unfold ConstructorArgs.argumentEnd; rw [a.encoded_length]; omega)
    (by omega) (constructorNameMemory_symbol a hbound hsmall).length
    (constructorNameMemory_free a hsmall)
    (fun h => hsymbol ((a.symbolAllocationFits hsmall hname).mp h)) rd

theorem constructorDecodeSymbol {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat} (a : ConstructorArgs)
    (hbound : 23666 + a.encoded.length < UInt256.size)
    (hsmall : a.argumentEnd < 2 ^ 64) (hname : a.nameEnd < 2 ^ 64)
    (hsymbol : a.stringsEnd < 2 ^ 64)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨2690⟩
      [UInt256.ofNat (704 + paddedSize a.name.size), UInt256.ofNat a.argumentEnd, ⟨150⟩,
        UInt256.ofNat a.argumentEnd, UInt256.ofNat a.owner.val, a.initialTimelock,
        UInt256.ofNat a.morpho.val, UInt256.ofNat a.asset.val]
      (constructorNameMemory a) aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨150⟩
      [UInt256.ofNat a.nameEnd, UInt256.ofNat a.argumentEnd, UInt256.ofNat a.owner.val,
        a.initialTimelock, UInt256.ofNat a.morpho.val, UInt256.ofNat a.asset.val]
      (constructorStringsMemory a) aw' rdata σ k' C' := by
  have hs := (a.string_sizes_small hsmall).2
  have hptr : a.nameEnd < UInt256.size := by change _ < 2 ^ 256; omega
  obtain ⟨aw1, k1, C1, r1⟩ := constructorStringReturn (ptr := UInt256.ofNat a.nameEnd)
    (704 + paddedSize a.name.size)
    a.argumentEnd a.symbol.size (by simp) hs
    (by have hp : a.symbol.size ≤ paddedSize a.symbol.size := by unfold paddedSize; omega
        unfold ConstructorArgs.argumentEnd; rw [a.encoded_length]; omega)
    (by omega) (constructorNameMemory_symbol a hbound hsmall).length
    (constructorNameMemory_free a hsmall)
    ((a.symbolAllocationFits hsmall hname).mpr hsymbol) (by native_decide) rd
  rw [stringAllocationCursor _ _ hs, UInt256.toNat_ofNat_of_lt hptr] at r1
  exact ⟨aw1, k1, C1, r1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
