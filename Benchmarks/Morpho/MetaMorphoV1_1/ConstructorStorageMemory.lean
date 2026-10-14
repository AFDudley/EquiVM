import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStorageWrite

/-! Storage initialization only changes scratch memory and preserves the allocated inputs. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

theorem constructorStorageMemoryPreserved {mem mem' : ByteArray} (symbol : Bool)
    (hmem : 96 ≤ mem.size) (hm : mem' = mem ∨ mem' = constructorStorageScratch mem symbol) :
    (∀ limit, ByteMemoryPrefix mem mem' limit) ∧ memLoad ⟨64⟩ mem' = memLoad ⟨64⟩ mem := by
  rcases hm with rfl | rfl
  · exact ⟨fun _ => .refl _ _, rfl⟩
  · refine ⟨fun limit => byteMemoryPrefix_writeWord mem 0 limit _ (.inr (by decide)), ?_⟩
    exact memLoad_write_disjoint mem 0 ⟨64⟩ (constructorMetadataSlot symbol) hmem (.inr (by decide))

theorem constructorSymbolEntry {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (ptr : Nat)
    (hload : memLoad (constructorMetadataPtr ptr true) mem = ⟨0⟩)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨338⟩
      (constructorMetadataTail a ptr false) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨356⟩
      (constructorMetadataPtr ptr true :: ⟨0⟩ :: constructorMetadataTail a ptr true)
      mem aw' rdata σ k' C' := by
  have hc : UInt256.gt (memLoad (constructorMetadataPtr ptr true) mem)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)) =
      ⟨0⟩ := by rw [hload]; decide
  obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1Creation_block_338_fallthrough_packed (by simp) hc rd
  change RD _ I g s0 ⟨356⟩
    (constructorMetadataPtr ptr true :: memLoad (constructorMetadataPtr ptr true) mem ::
      constructorMetadataTail a ptr true) mem aw1 rdata σ k1 C1 at r1
  rw [hload] at r1
  exact ⟨aw1, k1, C1, r1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
