import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorUnderlying
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorZeroMemory

/-! Literal reads preserved by the decimals call and the first immutable stores. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

theorem constructorPreservedLiteralReads (base mem : ByteArray) (ptr : Nat)
    (hlo : 96 ≤ ptr) (hptr : ptr + 160 < UInt256.size)
    (hp : ByteMemoryPrefix (constructorVersionMemory base ptr) mem (ptr + 160)) :
    ptr + 160 ≤ mem.size ∧
    memLoad (UInt256.ofNat ptr) mem = ⟨0⟩ ∧
    memLoad (UInt256.ofNat (ptr + 32)) mem = ⟨0⟩ ∧
    memLoad (UInt256.ofNat (ptr + 96)) mem = ⟨1⟩ ∧
    memLoad (UInt256.ofNat (ptr + 128)) mem = UInt256.shiftLeft (UInt256.ofNat 49) ⟨248⟩ := by
  have hm : ptr + 160 ≤ (constructorVersionMemory base ptr).size := by
    rw [constructorVersionMemory, writeWord_sparse_size]
    omega
  have he0 := (constructorVersionMemory_empty base ptr ⟨0, by decide⟩ hlo hptr).preserve hp
    (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; simpa using hlo)
    (by rw [UInt256.toNat_ofNat_of_lt (by omega), ByteArray.size_empty]; omega)
  have he1 := (constructorVersionMemory_empty base ptr ⟨1, by decide⟩ hlo hptr).preserve hp
    (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)
    (by rw [UInt256.toNat_ofNat_of_lt (by omega), ByteArray.size_empty]; omega)
  have hv := (constructorVersionMemory_version base ptr hptr).preserve hp
    (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)
    (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; change ptr + 96 + 32 + 1 ≤ ptr + 160; omega)
  refine ⟨le_trans hm hp.size, ?_, ?_, hv.length, ?_⟩
  · simpa only [Nat.mul_zero, Nat.add_zero, ByteArray.size_empty] using he0.length
  · simpa only [Nat.mul_one, ByteArray.size_empty] using he1.length
  · rw [hp.load (UInt256.ofNat (ptr + 128))
      (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)
      (by rw [UInt256.toNat_ofNat_of_lt (by omega)])
      (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)]
    exact memLoad_write_same _ _ _ _ (UInt256.toNat_ofNat_of_lt (by omega))

theorem constructorAssetMemory_load (mem : ByteArray) (asset : AccountAddress)
    (decimals read : UInt256) (hlo : 192 ≤ read.toNat) (hin : read.toNat + 32 ≤ mem.size) :
    memLoad read (constructorAssetMemory mem asset decimals) = memLoad read mem := by
  rw [constructorAssetMemory, Reasoning.Theory.writeWord,
    memLoad_write_disjoint _ 128 read _ (by rw [writeWord_sparse_size]; omega) (.inr (by omega)),
    Reasoning.Theory.writeWord,
    memLoad_write_disjoint _ 160 read _ hin (.inr hlo)]

theorem constructorAssetMemory_free (mem : ByteArray) (asset : AccountAddress)
    (decimals : UInt256) (hmem : 96 ≤ mem.size) :
    memLoad ⟨64⟩ (constructorAssetMemory mem asset decimals) = memLoad ⟨64⟩ mem := by
  rw [constructorAssetMemory, Reasoning.Theory.writeWord,
    memLoad_write_disjoint _ 128 ⟨64⟩ _ (by rw [writeWord_sparse_size]; change 96 ≤ _; omega) (.inl (by decide)),
    Reasoning.Theory.writeWord,
    memLoad_write_disjoint _ 160 ⟨64⟩ _ hmem (.inl (by decide))]

end Benchmarks.Morpho.MetaMorphoV1_1
