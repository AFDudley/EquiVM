import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorLiteralBuffers
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorEntry
import Benchmarks.Morpho.MetaMorphoV1_1.StringHeader
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_002
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_010

/-! Decode and validate the old ERC20 metadata headers before initializing them. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

def constructorMetadataSlot (symbol : Bool) : UInt256 := if symbol then ⟨4⟩ else ⟨3⟩
def constructorMetadataHeaderPC (symbol : Bool) : UInt256 := if symbol then ⟨356⟩ else ⟨260⟩
def constructorMetadataCheckPC (symbol : Bool) : UInt256 := if symbol then ⟨373⟩ else ⟨277⟩
def constructorMetadataClearPC (symbol : Bool) : UInt256 := if symbol then ⟨382⟩ else ⟨286⟩
def constructorMetadataPtr (ptr : Nat) (symbol : Bool) : UInt256 :=
  UInt256.ofNat (ptr + if symbol then 64 else 32)

def constructorMetadataTail (a : ConstructorArgs) (ptr : Nat) (symbol : Bool) : List UInt256 :=
  (if symbol then [] else [UInt256.ofNat (ptr + 64)]) ++
    [UInt256.ofNat ptr, UInt256.ofNat (ptr + 96), UInt256.ofNat a.owner.val,
      UInt256.ofNat a.morpho.val, UInt256.ofNat a.argumentEnd, UInt256.ofNat a.nameEnd,
      UInt256.ofNat a.asset.val, a.initialTimelock, ⟨32⟩, ⟨64⟩]

theorem constructorMetadataHeader {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr : UInt256} {R : List UInt256} (symbol : Bool)
    (hstack : R.length + 5 ≤ 1024)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorMetadataHeaderPC symbol)
      (ptr :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorMetadataCheckPC symbol)
      (UInt256.land (solcSlotWord σ I (constructorMetadataSlot symbol)) ⟨1⟩ :: ptr ::
        storageStringLength (solcSlotWord σ I (constructorMetadataSlot symbol)) :: R)
      mem aw' rdata σ k' C' := by
  have hshift := wordShiftRight_eq_div (solcSlotWord σ I (constructorMetadataSlot symbol)) 1 (by decide)
  by_cases hz : UInt256.land (solcSlotWord σ I (constructorMetadataSlot symbol)) ⟨1⟩ = ⟨0⟩
  · cases symbol with
    | false =>
      change UInt256.land (solcSlotWord σ I ⟨3⟩) ⟨1⟩ = ⟨0⟩ at hz
      change UInt256.shiftRight (solcSlotWord σ I ⟨3⟩) (UInt256.ofNat 1) =
        UInt256.div (solcSlotWord σ I ⟨3⟩) ⟨2⟩ at hshift
      obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_260_taken_packed hstack
        (by change UInt256.isZero (UInt256.land (solcSlotWord σ I ⟨3⟩) ⟨1⟩) ≠ ⟨0⟩
            rw [hz]; decide) (by native_decide) rd
      obtain ⟨aw2, k2, C2, r2⟩ := metaMorphoV1_1Creation_block_2598_packed
        (by omega) (by native_decide) r1
      refine ⟨aw2, k2, C2, ?_⟩
      change RD _ I g s0 ⟨277⟩ (UInt256.land (solcSlotWord σ I ⟨3⟩) ⟨1⟩ :: ptr ::
        UInt256.land (UInt256.ofNat 127)
          (UInt256.shiftRight (solcSlotWord σ I ⟨3⟩) (UInt256.ofNat 1)) :: R) _ aw2 _ σ k2 C2 at r2
      simpa only [constructorMetadataSlot, Bool.false_eq_true, if_false, hshift,
        u256_land_comm (UInt256.ofNat 127), storageStringLength, if_pos hz] using r2
    | true =>
      change UInt256.land (solcSlotWord σ I ⟨4⟩) ⟨1⟩ = ⟨0⟩ at hz
      change UInt256.shiftRight (solcSlotWord σ I ⟨4⟩) (UInt256.ofNat 1) =
        UInt256.div (solcSlotWord σ I ⟨4⟩) ⟨2⟩ at hshift
      obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_356_taken_packed hstack
        (by change UInt256.isZero (UInt256.land (solcSlotWord σ I ⟨4⟩) ⟨1⟩) ≠ ⟨0⟩
            rw [hz]; decide) (by native_decide) rd
      obtain ⟨aw2, k2, C2, r2⟩ := metaMorphoV1_1Creation_block_2386_packed
        (by omega) (by native_decide) r1
      refine ⟨aw2, k2, C2, ?_⟩
      change RD _ I g s0 ⟨373⟩ (UInt256.land (solcSlotWord σ I ⟨4⟩) ⟨1⟩ :: ptr ::
        UInt256.land (UInt256.ofNat 127)
          (UInt256.shiftRight (solcSlotWord σ I ⟨4⟩) (UInt256.ofNat 1)) :: R) _ aw2 _ σ k2 C2 at r2
      simpa only [constructorMetadataSlot, if_true, hshift,
        u256_land_comm (UInt256.ofNat 127), storageStringLength, if_pos hz] using r2
  · cases symbol with
    | false =>
      obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1Creation_block_260_fallthrough_packed hstack
        (isZero_eq_zero_of_ne hz) rd
      change UInt256.land (solcSlotWord σ I ⟨3⟩) ⟨1⟩ ≠ ⟨0⟩ at hz
      change UInt256.shiftRight (solcSlotWord σ I ⟨3⟩) (UInt256.ofNat 1) =
        UInt256.div (solcSlotWord σ I ⟨3⟩) ⟨2⟩ at hshift
      change RD _ I g s0 ⟨277⟩ (UInt256.land (solcSlotWord σ I ⟨3⟩) ⟨1⟩ :: ptr ::
        UInt256.shiftRight (solcSlotWord σ I ⟨3⟩) (UInt256.ofNat 1) :: R) _ aw1 _ σ k1 C1 at r1
      refine ⟨aw1, k1, C1, ?_⟩
      simpa only [constructorMetadataSlot, Bool.false_eq_true, if_false, hshift,
        storageStringLength, if_neg hz] using r1
    | true =>
      obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1Creation_block_356_fallthrough_packed hstack
        (isZero_eq_zero_of_ne hz) rd
      change UInt256.land (solcSlotWord σ I ⟨4⟩) ⟨1⟩ ≠ ⟨0⟩ at hz
      change UInt256.shiftRight (solcSlotWord σ I ⟨4⟩) (UInt256.ofNat 1) =
        UInt256.div (solcSlotWord σ I ⟨4⟩) ⟨2⟩ at hshift
      change RD _ I g s0 ⟨373⟩ (UInt256.land (solcSlotWord σ I ⟨4⟩) ⟨1⟩ :: ptr ::
        UInt256.shiftRight (solcSlotWord σ I ⟨4⟩) (UInt256.ofNat 1) :: R) _ aw1 _ σ k1 C1 at r1
      refine ⟨aw1, k1, C1, ?_⟩
      simpa only [constructorMetadataSlot, if_true, hshift, storageStringLength, if_neg hz] using r1

theorem constructorMetadataValid {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} (a : ConstructorArgs) (ptr : Nat) (symbol : Bool)
    (hvalid : storageStringValid (solcSlotWord σ I (constructorMetadataSlot symbol)))
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorMetadataCheckPC symbol)
      (UInt256.land (solcSlotWord σ I (constructorMetadataSlot symbol)) ⟨1⟩ ::
        constructorMetadataPtr ptr symbol ::
        storageStringLength (solcSlotWord σ I (constructorMetadataSlot symbol)) ::
        ⟨0⟩ :: constructorMetadataTail a ptr symbol) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorMetadataClearPC symbol)
      (constructorMetadataPtr ptr symbol ::
        storageStringLength (solcSlotWord σ I (constructorMetadataSlot symbol)) ::
        ⟨0⟩ :: constructorMetadataTail a ptr symbol) mem aw' rdata σ k' C' := by
  have hc := u256_eq_of_ne (Ne.symm hvalid)
  cases symbol with
  | false =>
    exact metaMorphoV1_1Creation_block_277_fallthrough_packed (by simp) hc rd
  | true =>
    exact metaMorphoV1_1Creation_block_373_fallthrough_packed (by simp) hc rd

theorem constructorMetadataInvalid {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} (a : ConstructorArgs) (ptr : Nat) (symbol : Bool)
    (hbad : ¬ storageStringValid (solcSlotWord σ I (constructorMetadataSlot symbol)))
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorMetadataCheckPC symbol)
      (UInt256.land (solcSlotWord σ I (constructorMetadataSlot symbol)) ⟨1⟩ ::
        constructorMetadataPtr ptr symbol ::
        storageStringLength (solcSlotWord σ I (constructorMetadataSlot symbol)) ::
        ⟨0⟩ :: constructorMetadataTail a ptr symbol) mem aw rdata σ k C) :
    RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0 := by
  have he : UInt256.lt (storageStringLength (solcSlotWord σ I (constructorMetadataSlot symbol))) ⟨32⟩ =
      UInt256.land (solcSlotWord σ I (constructorMetadataSlot symbol)) ⟨1⟩ :=
    (Classical.not_not.mp hbad).symm
  have hc : UInt256.eq
      (UInt256.lt (storageStringLength (solcSlotWord σ I (constructorMetadataSlot symbol))) ⟨32⟩)
      (UInt256.land (solcSlotWord σ I (constructorMetadataSlot symbol)) ⟨1⟩) ≠ ⟨0⟩ := by
    rw [he, u256_eq_refl]; decide
  cases symbol with
  | false =>
    have r1 := metaMorphoV1_1Creation_block_277_taken (by simp)
      hc (by native_decide) rd
    exact metaMorphoV1_1Creation_block_1824 (by simp [metaMorphoV1_1Creation_block_277_taken_stack]) r1
  | true =>
    have r1 := metaMorphoV1_1Creation_block_373_taken (by simp)
      hc (by native_decide) rd
    exact metaMorphoV1_1Creation_block_1824 (by simp [metaMorphoV1_1Creation_block_373_taken_stack]) r1

theorem constructorVersionEntry {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (ptr : Nat) (hlo : 96 ≤ ptr) (hptr : ptr + 160 < UInt256.size)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨229⟩
      [UInt256.ofNat (ptr + 32), UInt256.ofNat (ptr + 64), UInt256.ofNat ptr,
        UInt256.ofNat (ptr + 96), UInt256.ofNat a.owner.val, UInt256.ofNat a.morpho.val,
        UInt256.ofNat a.argumentEnd, UInt256.ofNat a.nameEnd, UInt256.ofNat a.asset.val,
        a.initialTimelock, ⟨32⟩, ⟨64⟩]
      (constructorLiteralMemory mem ptr) aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨260⟩
      (constructorMetadataPtr ptr false :: ⟨0⟩ :: constructorMetadataTail a ptr false)
      (constructorVersionMemory mem ptr) aw' rdata σ k' C' := by
  have hm : metaMorphoV1_1Creation_block_229_fallthrough_memory
      (mem := constructorLiteralMemory mem ptr) (x3 := UInt256.ofNat (ptr + 96)) (x10 := ⟨32⟩) =
      constructorVersionMemory mem ptr := by
    simp only [metaMorphoV1_1Creation_block_229_fallthrough_memory,
      UInt256.toNat_ofNat_of_lt (show ptr + 96 < UInt256.size by omega),
      show (⟨32⟩ : UInt256) = UInt256.ofNat 32 from rfl, ofNat_add_words,
      UInt256.toNat_ofNat_of_lt (show ptr + 96 + 32 < UInt256.size by omega)]
    rfl
  have hl : memLoad (UInt256.ofNat (ptr + 32)) (constructorVersionMemory mem ptr) = ⟨0⟩ :=
    (constructorVersionMemory_empty mem ptr ⟨1, by decide⟩ hlo hptr).length
  have hc : UInt256.gt
      (memLoad (UInt256.ofNat (ptr + 32))
        (metaMorphoV1_1Creation_block_229_fallthrough_memory
          (mem := constructorLiteralMemory mem ptr) (x3 := UInt256.ofNat (ptr + 96)) (x10 := ⟨32⟩)))
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)) = ⟨0⟩ := by
    rw [hm, hl]; native_decide
  obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1Creation_block_229_fallthrough_packed (by decide) hc rd
  simp only [metaMorphoV1_1Creation_block_229_fallthrough_stack] at r1
  change RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨260⟩
    (constructorMetadataPtr ptr false :: memLoad (UInt256.ofNat (ptr + 32))
      (metaMorphoV1_1Creation_block_229_fallthrough_memory
        (mem := constructorLiteralMemory mem ptr) (x3 := UInt256.ofNat (ptr + 96)) (x10 := ⟨32⟩)) ::
      constructorMetadataTail a ptr false)
    (metaMorphoV1_1Creation_block_229_fallthrough_memory
      (mem := constructorLiteralMemory mem ptr) (x3 := UInt256.ofNat (ptr + 96)) (x10 := ⟨32⟩))
    aw1 rdata σ k1 C1 at r1
  rw [hm, hl] at r1
  exact ⟨aw1, k1, C1, r1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
