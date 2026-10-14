import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateEventStatic
import Benchmarks.Morpho.MetaMorphoV1_1.StructReturnMemory
import Benchmarks.Morpho.MetaMorphoV1_1.CheckedArithmetic

/-! Both reallocation events encode two words at the current free-memory cursor. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def reallocateEventMemory (mem : ByteArray) (ptr assets shares : UInt256) : ByteArray :=
  writeWord (writeWord mem ptr.toNat assets) (ptr.toNat + 32) shares

theorem reallocateEventMemory_prefix (mem : ByteArray) (ptr assets shares : UInt256) :
    MemoryPrefix mem (reallocateEventMemory mem ptr assets shares) ptr.toNat :=
  (memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _))).trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (.inl (by omega)))

theorem reallocateEventMemory_free {mem : ByteArray} {ptr assets shares : UInt256}
    (hmem : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) :
    memLoad ⟨64⟩ (reallocateEventMemory mem ptr assets shares) = memLoad ⟨64⟩ mem := by
  rw [reallocateEventMemory, memLoad_write_above _ _ _ _
      (by rw [writeWord_sparse_size]; change 64 + 32 ≤ _; omega) (by change 64 + 32 ≤ ptr.toNat + 32; omega),
    memLoad_write_above mem ⟨64⟩ ptr.toNat assets (by exact hmem) (by change 64 + 32 ≤ ptr.toNat; omega)]

set_option maxRecDepth 2000 in
theorem reallocateEventRuntime {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr scratch shares id total amount : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (supply : Bool) (hstack : R.length + 7 ≤ 1024)
    (hperm : I.perm = true) (hfree : memLoad ⟨64⟩ mem = ptr) (hptr : ptr.toNat < 2 ^ 64)
    (rd : RD (deployedRuntime v) I g s0 (if supply then ⟨6630⟩ else ⟨6322⟩)
      (scratch :: shares :: id :: total :: amount :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12077⟩ (total :: amount :: R)
      (reallocateEventMemory mem ptr amount shares) aw' rdata σ k' C' := by
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  have hp : (ptr + UInt256.ofNat 32).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)
  cases supply with
  | false =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_6322_packed
        (immWords := wordsOf (immStore v)) hstack hperm
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      exact ⟨aw1, k1, C1, by simpa only [metaMorphoV1_1_block_6322_stack,
        metaMorphoV1_1_block_6322_memory, hf, hp, reallocateEventMemory, Reasoning.Theory.writeWord] using h1⟩
  | true =>
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_6630_packed
        (immWords := wordsOf (immStore v)) hstack hperm
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      exact ⟨aw1, k1, C1, by simpa only [metaMorphoV1_1_block_6630_stack,
        metaMorphoV1_1_block_6630_memory, hf, hp, reallocateEventMemory, Reasoning.Theory.writeWord] using h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
