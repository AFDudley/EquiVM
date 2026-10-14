import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorAssetInit
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDomainMemory

/-! Carry the constructor's literal buffers and free pointer through immutable initialization. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

theorem constructorAssetReadyMemory_buffer {mem bytes : ByteArray} {ptr : UInt256}
    (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (buffer : BytesBuffer mem ptr bytes) (hlo : 384 ≤ ptr.toNat) :
    BytesBuffer (constructorAssetReadyMemory mem a ok out) ptr bytes :=
  ((buffer.writeWord 160 _ (.inr (by omega))).writeWord 128 _ (.inr (by omega))).writeWord
    352 ⟨0⟩ (.inr hlo)

theorem constructorAssetReadyMemory_free (mem : ByteArray) (a : ConstructorArgs)
    (ok : Bool) (out : ByteArray) (hmem : 96 ≤ mem.size) :
    memLoad ⟨64⟩ (constructorAssetReadyMemory mem a ok out) = memLoad ⟨64⟩ mem := by
  unfold constructorAssetReadyMemory
  rw [memLoad_writeWord_disjoint _ 352 ⟨64⟩ _
    (by simp only [constructorAssetMemory, writeWord_sparse_size]; change 96 ≤ _; omega)
    (.inl (by decide)), constructorAssetMemory_free mem a.asset _ hmem]

theorem constructorDomainInputs (base mem : ByteArray) (a : ConstructorArgs)
    (ok : Bool) (out : ByteArray) (hlo : 480 ≤ a.stringsEnd)
    (hptr : a.stringsEnd + 160 < UInt256.size)
    (hp : ByteMemoryPrefix (constructorVersionMemory base a.stringsEnd) mem (a.stringsEnd + 160)) :
    BytesBuffer (constructorAssetReadyMemory mem a ok out) (UInt256.ofNat a.stringsEnd) ByteArray.empty ∧
    BytesBuffer (constructorAssetReadyMemory mem a ok out) (UInt256.ofNat (a.stringsEnd + 96))
      "1".toUTF8 := by
  have hpn : (UInt256.ofNat a.stringsEnd).toNat = a.stringsEnd :=
    UInt256.toNat_ofNat_of_lt (by omega)
  have hvn : (UInt256.ofNat (a.stringsEnd + 96)).toNat = a.stringsEnd + 96 :=
    UInt256.toNat_ofNat_of_lt (by omega)
  have he : BytesBuffer (constructorVersionMemory base a.stringsEnd)
      (UInt256.ofNat a.stringsEnd) ByteArray.empty := by
    simpa only [Nat.mul_zero, Nat.add_zero] using
      constructorVersionMemory_empty base a.stringsEnd ⟨0, by decide⟩ (by omega) hptr
  have hv := constructorVersionMemory_version base a.stringsEnd hptr
  refine ⟨constructorAssetReadyMemory_buffer a ok out
    (he.preserve hp (by rw [hpn]; omega) (by rw [hpn, ByteArray.size_empty]; omega))
    (by rw [hpn]; omega), ?_⟩
  exact constructorAssetReadyMemory_buffer a ok out
    (hv.preserve hp (by rw [hvn]; omega) (by rw [hvn]; change a.stringsEnd + 96 + 32 + 1 ≤ _; omega))
    (by rw [hvn]; omega)

end Benchmarks.Morpho.MetaMorphoV1_1
