import Benchmarks.Morpho.MetaMorphoV1_1.SparseCopyMemory
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorEncoding
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeWriteWindow

/-! Copy the creation artifact's runtime window and patch its declared immutable sites. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode metaMorphoV1_1Bytecode
set_option autoImplicit false

def constructorRuntimeSites : List (Nat × Nat) :=
  immutableReferences.zipIdx.flatMap fun ((_, sites), i) ↦
    sites.map fun off ↦ (off, 128 + 32 * i)

def constructorRuntimeWords (w : Nat → UInt256) : String → UInt256
  | "_asset" => w 128
  | "_underlyingDecimals" => w 160
  | "_cachedDomainSeparator" => w 192
  | "_cachedChainId" => w 224
  | "_cachedThis" => w 256
  | "_hashedName" => w 288
  | "_hashedVersion" => w 320
  | "_name" => w 352
  | "_version" => w 384
  | "MORPHO" => w 416
  | "DECIMALS_OFFSET" => w 448
  | _ => ⟨0⟩

theorem constructorRuntimeSites_length : constructorRuntimeSites.length = 32 := by decide

theorem constructorRuntimeSites_bounded :
    ∀ p ∈ constructorRuntimeSites, p.1 + 32 ≤ 19708 := by decide

theorem constructorRuntimeSites_layout (w : Nat → UInt256) :
    constructorRuntimeSites.map (fun (off, slot) ↦ (off, w slot)) =
      immutableLayout.writes (constructorRuntimeWords w) := rfl

def constructorRuntimeCopy (mem tail : ByteArray) (ptr : UInt256) : ByteArray :=
  (metaMorphoV1_1CreationBytecode ++ tail).write 3894 mem ptr.toNat 19708

def constructorRuntimePart (mem : ByteArray) (ptr : UInt256) (w : Nat → UInt256)
    (start count : Nat) : ByteArray :=
  writeCascade mem (((constructorRuntimeSites.drop start).take count).map fun (off, slot) ↦
    (ptr.toNat + off, w slot))

theorem constructorRuntimeCopy_prefix (mem tail : ByteArray) (ptr : UInt256) :
    MemoryPrefix mem (constructorRuntimeCopy mem tail ptr) ptr.toNat :=
  (byteMemoryPrefix_copy_sparse _ _ 3894 ptr.toNat 19708
    (by rw [ByteArray.size_append, metaMorphoV1_1CreationBytecode_size]; omega)).words

theorem constructorRuntimeCopy_size (mem tail : ByteArray) (ptr : UInt256) :
    (constructorRuntimeCopy mem tail ptr).size = max mem.size (ptr.toNat + 19708) :=
  copyWindow_sparse_size _ _ _ _ _ (by decide)
    (by rw [ByteArray.size_append, metaMorphoV1_1CreationBytecode_size]; omega)

theorem constructorRuntimeCopy_template (mem tail : ByteArray) (ptr : UInt256) :
    (constructorRuntimeCopy mem tail ptr).extract ptr.toNat (ptr.toNat + 19708) =
      metaMorphoV1_1Bytecode := by
  have hc : metaMorphoV1_1CreationBytecode.extract 3894 (3894 + 19708) = metaMorphoV1_1Bytecode := by
    native_decide
  exact (copyWindow_sparse_extract _ _ _ _ _ (by decide)
    (by rw [ByteArray.size_append, metaMorphoV1_1CreationBytecode_size]; omega)).trans
      ((byteArray_extract_append_left _ _ _ _ (by rw [metaMorphoV1_1CreationBytecode_size]; decide)).trans hc)

theorem constructorRuntimePart_prefix (mem : ByteArray) (ptr : UInt256)
    (w : Nat → UInt256) (start count : Nat) :
    MemoryPrefix mem (constructorRuntimePart mem ptr w start count) ptr.toNat := by
  apply memoryPrefix_sparse_cascade
  intro p hp
  obtain ⟨⟨off, slot⟩, _, rfl⟩ := List.mem_map.mp hp
  exact .inl (Nat.le_add_right _ _)

theorem constructorRuntimePart_compose (mem : ByteArray) (ptr : UInt256) (w : Nat → UInt256)
    (start count : Nat) :
    constructorRuntimePart (constructorRuntimePart mem ptr w 0 start) ptr w start count =
      constructorRuntimePart mem ptr w 0 (start + count) := by
  unfold constructorRuntimePart
  rw [List.drop_zero, ← writeCascade_append, ← List.map_append, List.take_add]

theorem constructorRuntimePart_return (mem tail : ByteArray) (ptr : UInt256) (w : Nat → UInt256) :
    (constructorRuntimePart (constructorRuntimeCopy mem tail ptr) ptr w 0 32).readWithPadding
      ptr.toNat 19708 = immutableLayout.runtime metaMorphoV1_1Bytecode (constructorRuntimeWords w) := by
  have hin : ptr.toNat + 19708 ≤ (constructorRuntimeCopy mem tail ptr).size := by
    rw [constructorRuntimeCopy_size]; omega
  have hs := (constructorRuntimePart_prefix (constructorRuntimeCopy mem tail ptr) ptr w 0 32).size
  rw [readWithPadding_eq_extract' _ _ _ (by decide) (by decide) (le_trans hin hs)]
  unfold constructorRuntimePart
  rw [List.drop_zero, List.take_of_length_le (by rw [constructorRuntimeSites_length])]
  have he := writeCascade_extract_window
    (constructorRuntimeCopy mem tail ptr) ptr.toNat 19708
    (constructorRuntimeSites.map fun (off, slot) ↦ (off, w slot)) hin (by
      intro p hp
      obtain ⟨⟨off, slot⟩, hsite, rfl⟩ := List.mem_map.mp hp
      exact constructorRuntimeSites_bounded (off, slot) hsite)
  simp only [List.map_map, Function.comp_def] at he
  apply he.trans
  rw [constructorRuntimeCopy_template, constructorRuntimeSites_layout]
  rfl

end Benchmarks.Morpho.MetaMorphoV1_1
