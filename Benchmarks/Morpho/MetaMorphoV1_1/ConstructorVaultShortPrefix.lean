import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultTopicMemory
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_005

/-! Prepare packed vault metadata and its event arguments without changing input memory. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

def constructorVaultShortPC (symbol : Bool) : UInt256 := if symbol then ⟨952⟩ else ⟨827⟩
def constructorVaultShortStorePC (symbol : Bool) : UInt256 := if symbol then ⟨979⟩ else ⟨854⟩
def constructorVaultEncodePC (symbol : Bool) : UInt256 := if symbol then ⟨999⟩ else ⟨874⟩
def constructorVaultEventPC (symbol : Bool) : UInt256 := if symbol then ⟨1010⟩ else ⟨885⟩

theorem constructorVaultShortSelect {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {junk len ptr : UInt256} (a : ConstructorArgs) (symbol : Bool) (hshort : len.toNat < 32)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultStorePC symbol)
      (junk :: len :: ptr :: constructorVaultTail a symbol) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorVaultShortPC symbol) (⟨32⟩ :: len :: ptr :: constructorVaultTail a symbol)
      mem aw' rdata σ k' C' := by
  have hc : UInt256.eq (UInt256.ofNat 1) (UInt256.gt len (UInt256.ofNat 31)) = ⟨0⟩ := by
    change UInt256.eq ⟨1⟩ (UInt256.lt ⟨31⟩ len) = ⟨0⟩
    rw [ult_zero (by change len.toNat ≤ 31; omega)]; decide
  cases symbol with
  | false => exact metaMorphoV1_1Creation_block_813_fallthrough_packed (by simp) hc rd
  | true => exact metaMorphoV1_1Creation_block_938_fallthrough_packed (by simp) hc rd

theorem constructorVaultShortZero {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr : UInt256} {R : List UInt256} (symbol : Bool) (hstack : R.length + 9 ≤ 1024)
    (hmem : 32 ≤ mem.size)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultShortPC symbol)
      (⟨32⟩ :: ⟨0⟩ :: ptr :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorVaultShortStorePC symbol)
      (⟨32⟩ :: ⟨0⟩ :: ⟨0⟩ :: ptr :: constructorVaultEventPC symbol :: stringSetTopic symbol :: R)
      mem aw' rdata σ k' C' := by
  cases symbol with
  | false =>
    obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1Creation_block_827_fallthrough_packed hstack rfl rd
    change RD _ I g s0 ⟨854⟩ (⟨32⟩ :: ⟨0⟩ :: ⟨0⟩ :: ptr :: ⟨885⟩ ::
      memLoad ⟨0⟩ ((metaMorphoV1_1CreationBytecode ++ tail).write
        (constructorVaultTopicOffset false) mem 0 32) :: R)
      (writeWord ((metaMorphoV1_1CreationBytecode ++ tail).write
        (constructorVaultTopicOffset false) mem 0 32) 0 (memLoad ⟨0⟩ mem)) aw1 rdata σ k1 C1 at r1
    rw [constructorVaultTopicRead, constructorVaultTopicRestore tail mem false hmem] at r1
    exact ⟨aw1, k1, C1, r1⟩
  | true =>
    obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1Creation_block_952_fallthrough_packed hstack rfl rd
    change RD _ I g s0 ⟨979⟩ (⟨32⟩ :: ⟨0⟩ :: ⟨0⟩ :: ptr :: ⟨1010⟩ ::
      memLoad ⟨0⟩ ((metaMorphoV1_1CreationBytecode ++ tail).write
        (constructorVaultTopicOffset true) mem 0 32) :: R)
      (writeWord ((metaMorphoV1_1CreationBytecode ++ tail).write
        (constructorVaultTopicOffset true) mem 0 32) 0 (memLoad ⟨0⟩ mem)) aw1 rdata σ k1 C1 at r1
    rw [constructorVaultTopicRead, constructorVaultTopicRestore tail mem true hmem] at r1
    exact ⟨aw1, k1, C1, r1⟩

theorem constructorVaultShortNonzero {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {len ptr : UInt256} {R : List UInt256} (symbol : Bool) (hstack : R.length + 9 ≤ 1024)
    (hmem : 32 ≤ mem.size) (hnz : len ≠ ⟨0⟩)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultShortPC symbol)
      (⟨32⟩ :: len :: ptr :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorVaultShortStorePC symbol)
      (⟨0⟩ :: memLoad (ptr + ⟨32⟩) mem :: len :: ptr ::
        constructorVaultEventPC symbol :: stringSetTopic symbol :: R) mem aw' rdata σ k' C' := by
  cases symbol with
  | false =>
    obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1Creation_block_827_taken_packed
      hstack hnz (by native_decide) rd
    change RD _ I g s0 ⟨1874⟩ (⟨32⟩ :: ⟨0⟩ :: len :: ptr :: ⟨885⟩ ::
      memLoad ⟨0⟩ ((metaMorphoV1_1CreationBytecode ++ tail).write
        (constructorVaultTopicOffset false) mem 0 32) :: R)
      (writeWord ((metaMorphoV1_1CreationBytecode ++ tail).write
        (constructorVaultTopicOffset false) mem 0 32) 0 (memLoad ⟨0⟩ mem)) aw1 rdata σ k1 C1 at r1
    rw [constructorVaultTopicRead, constructorVaultTopicRestore tail mem false hmem] at r1
    exact metaMorphoV1_1Creation_block_1874_packed
      (by simp only [List.length_cons]; omega) (by native_decide) r1
  | true =>
    obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1Creation_block_952_taken_packed
      hstack hnz (by native_decide) rd
    change RD _ I g s0 ⟨1617⟩ (⟨32⟩ :: ⟨0⟩ :: len :: ptr :: ⟨1010⟩ ::
      memLoad ⟨0⟩ ((metaMorphoV1_1CreationBytecode ++ tail).write
        (constructorVaultTopicOffset true) mem 0 32) :: R)
      (writeWord ((metaMorphoV1_1CreationBytecode ++ tail).write
        (constructorVaultTopicOffset true) mem 0 32) 0 (memLoad ⟨0⟩ mem)) aw1 rdata σ k1 C1 at r1
    rw [constructorVaultTopicRead, constructorVaultTopicRestore tail mem true hmem] at r1
    exact metaMorphoV1_1Creation_block_1617_packed
      (by simp only [List.length_cons]; omega) (by native_decide) r1

theorem constructorVaultShortReady {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata bytes : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {junk ptr : UInt256} (a : ConstructorArgs) (symbol : Bool)
    (buffer : StringBuffer mem ptr.toNat bytes)
    (hfit : ptr.toNat + 32 + bytes.size < UInt256.size) (hshort : bytes.size < 32)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultStorePC symbol)
      (junk :: UInt256.ofNat bytes.size :: ptr :: constructorVaultTail a symbol) mem aw rdata σ k C) :
    ∃ junk' word aw' k' C', stringPackedHeader word (UInt256.ofNat bytes.size) =
      solidityShortBytesWord bytes ∧
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultShortStorePC symbol)
        (junk' :: word :: UInt256.ofNat bytes.size :: ptr :: constructorVaultEventPC symbol ::
          stringSetTopic symbol :: constructorVaultTail a symbol) mem aw' rdata σ k' C' := by
  have hn : (UInt256.ofNat bytes.size).toNat = bytes.size :=
    UInt256.toNat_ofNat_of_lt (by omega)
  have hm : 32 ≤ mem.size := by have hb := buffer.size; omega
  obtain ⟨_, _, _, r1⟩ := constructorVaultShortSelect a symbol (by omega) rd
  by_cases hz : bytes.size = 0
  · have he : bytes = ByteArray.empty := ByteArray.ext (Array.size_eq_zero_iff.mp hz)
    rw [hz] at r1
    obtain ⟨aw2, k2, C2, r2⟩ := constructorVaultShortZero symbol
      (by cases symbol <;> simp [constructorVaultTail]) hm r1
    refine ⟨⟨32⟩, ⟨0⟩, aw2, k2, C2, ?_, ?_⟩
    · rw [he]; exact stringPackedHeader_empty
    · simpa only [hz] using r2
  · have hnz : UInt256.ofNat bytes.size ≠ (⟨0⟩ : UInt256) := by
      intro h
      have hnat := congrArg UInt256.toNat h
      rw [hn] at hnat
      exact hz hnat
    obtain ⟨aw2, k2, C2, r2⟩ := constructorVaultShortNonzero symbol
      (by cases symbol <;> simp [constructorVaultTail]) hm hnz r1
    exact ⟨⟨0⟩, _, aw2, k2, C2, buffer.packedHeader hfit hshort, r2⟩

end Benchmarks.Morpho.MetaMorphoV1_1
