import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorSetTimelockInit

/-! The decoded constructor metadata has enough materialized memory for padded string reads. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] ConstructorArgs.encoded
set_option autoImplicit false

-- LIBRARY CANDIDATE: a byte buffer with its padded capacity is a storage-writer string buffer.
theorem SourceMemory.BytesBuffer.stringBuffer {mem bytes : ByteArray} {ptr : UInt256}
    (buffer : BytesBuffer mem ptr bytes)
    (hpad : ptr.toNat + 32 + paddedSize bytes.size ≤ mem.size) :
    StringBuffer mem ptr.toNat bytes :=
  ⟨hpad, by simpa only [u256_ofNat_toNat] using buffer.length, buffer.data⟩

theorem constructorTimelockMemory_stringBuffers {mem : ByteArray} (a : ConstructorArgs)
    (ok : Bool) (out : ByteArray) (I : ExecutionEnv)
    (hsmall : a.argumentEnd < 2 ^ 64) (hname : a.nameEnd < 2 ^ 64)
    (hcursor : a.stringsEnd ≤ (constructorDecimalsCursor a out).toNat)
    (hn : BytesBuffer (constructorTimelockMemory mem a ok out I) (UInt256.ofNat a.argumentEnd) a.name)
    (hv : BytesBuffer (constructorTimelockMemory mem a ok out I) (UInt256.ofNat a.nameEnd) a.symbol) :
    StringBuffer (constructorTimelockMemory mem a ok out I) a.argumentEnd a.name ∧
    StringBuffer (constructorTimelockMemory mem a ok out I) a.nameEnd a.symbol := by
  have hnptr : (UInt256.ofNat a.argumentEnd).toNat = a.argumentEnd :=
    UInt256.toNat_ofNat_of_lt (by change a.argumentEnd < 2 ^ 256; omega)
  have hvptr : (UInt256.ofNat a.nameEnd).toNat = a.nameEnd :=
    UInt256.toNat_ofNat_of_lt (by change a.nameEnd < 2 ^ 256; omega)
  have hmem : (constructorDecimalsCursor a out).toNat + 224 ≤
      (constructorTimelockMemory mem a ok out I).size := by
    rw [constructorTimelockMemory, writeWord_sparse_size]; omega
  have hnend : a.argumentEnd + 32 + paddedSize a.name.size ≤ a.stringsEnd := by
    unfold ConstructorArgs.stringsEnd ConstructorArgs.nameEnd; omega
  have hvend : a.nameEnd + 32 + paddedSize a.symbol.size = a.stringsEnd := rfl
  have hn' := hn.stringBuffer (by rw [hnptr]; omega)
  have hv' := hv.stringBuffer (by rw [hvptr]; omega)
  exact ⟨by simpa only [hnptr] using hn', by simpa only [hvptr] using hv'⟩

theorem constructorTimelockMemory_free (mem : ByteArray) (a : ConstructorArgs)
    (ok : Bool) (out : ByteArray) (I : ExecutionEnv)
    (hcursor : 96 ≤ (constructorDecimalsCursor a out).toNat) :
    memLoad ⟨64⟩ (constructorTimelockMemory mem a ok out I) =
      UInt256.ofNat ((constructorDecimalsCursor a out).toNat + 192) := by
  have hm : 96 ≤ (constructorDomainReadyMemory mem a ok out I).size := by
    rw [constructorDomainReadyMemory, constructorDomainCachedMemory, writeWord_sparse_size]; omega
  rw [constructorTimelockMemory, memLoad_writeWord_disjoint _ _ ⟨64⟩ _ hm
    (.inl (by change 96 ≤ _; omega))]
  exact constructorDomainCachedMemory_free _ I _ hcursor

end Benchmarks.Morpho.MetaMorphoV1_1
