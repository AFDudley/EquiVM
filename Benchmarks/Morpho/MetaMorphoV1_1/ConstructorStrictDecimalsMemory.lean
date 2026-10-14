import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorMorphoRequest

/-! Immutable-word and cursor preservation across the strict decimals call. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def constructorStrictDecimalsMemory (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  writeWord (fixedReturnBuffer mem ptr out 32) 64 (nextCursor ptr ⟨32⟩)

theorem constructorMorphoMemory_prefix (mem : ByteArray) (morpho : AccountAddress) (ptr : UInt256)
    (hlo : 416 ≤ ptr.toNat) : ByteMemoryPrefix mem (constructorMorphoMemory mem morpho ptr) 416 :=
  (byteMemoryPrefix_writeWord mem 416 416 _ (.inl (le_refl _))).trans
    (byteMemoryPrefix_writeWord _ ptr.toNat 416 _ (.inl hlo))

theorem constructorMorphoMemory_morpho (mem : ByteArray) (morpho : AccountAddress) (ptr : UInt256)
    (hlo : 448 ≤ ptr.toNat) :
    memLoad ⟨416⟩ (constructorMorphoMemory mem morpho ptr) = UInt256.ofNat morpho.val := by
  rw [constructorMorphoMemory, memLoad_writeWord_disjoint _ ptr.toNat ⟨416⟩ _
    (by rw [writeWord_sparse_size]; change 448 ≤ _; omega) (.inl hlo)]
  exact memLoad_write_same _ _ _ _ rfl

theorem constructorMorphoMemory_free (mem : ByteArray) (morpho : AccountAddress) (ptr : UInt256)
    (hmem : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) :
    memLoad ⟨64⟩ (constructorMorphoMemory mem morpho ptr) = memLoad ⟨64⟩ mem := by
  rw [constructorMorphoMemory, memLoad_writeWord_disjoint _ ptr.toNat ⟨64⟩ _
    (by rw [writeWord_sparse_size]; change 96 ≤ _; omega) (.inl hlo)]
  exact memLoad_writeWord_disjoint mem 416 ⟨64⟩ _ hmem (.inl (by decide))

theorem constructorStrictDecimalsMemory_prefix {mem out : ByteArray} {ptr : UInt256}
    (hin : ptr.toNat ≤ mem.size) (hl : 32 ≤ out.size) (hout : out.size < UInt256.size) :
    ByteMemoryPrefix mem (constructorStrictDecimalsMemory mem ptr out) ptr.toNat := by
  rw [constructorStrictDecimalsMemory, fixedReturnBuffer_long _ _ _ hl hout]
  exact (byteMemoryPrefix_copy out mem 0 ptr.toNat 32 ptr.toNat (by omega) hin (le_refl _)).trans
    (byteMemoryPrefix_writeWord _ 64 ptr.toNat _ (.inr (by decide)))

theorem constructorStrictDecimalsMemory_free (mem : ByteArray) (ptr : UInt256) (out : ByteArray) :
    memLoad ⟨64⟩ (constructorStrictDecimalsMemory mem ptr out) = nextCursor ptr ⟨32⟩ :=
  memLoad_write_same _ _ _ _ rfl

theorem constructorStrictDecimalsMemory_word {mem out : ByteArray} {ptr : UInt256}
    (hin : ptr.toNat ≤ mem.size) (hlo : 96 ≤ ptr.toNat) (hp : ptr.toNat < 2 ^ 64)
    (hl : 32 ≤ out.size) (hout : out.size < UInt256.size) :
    memLoad ptr (constructorStrictDecimalsMemory mem ptr out) = calldataWord out 0 := by
  have hfit : ptr.toNat + 32 < UInt256.size := by change _ < 2 ^ 256; omega
  have hr := fixedReturnBuffer_load (off := 0) hin hl hout hfit (by decide)
  rw [show ptr + UInt256.ofNat 0 = ptr from uadd_zero_r ptr] at hr
  rw [constructorStrictDecimalsMemory, memLoad_writeWord_disjoint _ 64 ptr _
    (by rw [fixedReturnBuffer_size (by decide) hin hl hout]; omega) (.inr hlo)]
  exact hr

end Benchmarks.Morpho.MetaMorphoV1_1
