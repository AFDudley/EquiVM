import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultShortPrefix
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultDataLoop

/-! Store the final partial data word and long-string header before metadata event encoding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

def constructorVaultLongFinishPC (symbol more : Bool) : UInt256 :=
  if symbol then (if more then ⟨1698⟩ else ⟨1685⟩) else (if more then ⟨1955⟩ else ⟨1942⟩)

theorem constructorVaultLongPrepare {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {off cutoff stride slot len ptr : UInt256} {R : List UInt256} (symbol more : Bool)
    (hstack : R.length + 9 ≤ 1024) (hmem : 32 ≤ mem.size)
    (hcond : if more then UInt256.lt cutoff len ≠ ⟨0⟩ else UInt256.lt cutoff len = ⟨0⟩)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultDataExitPC symbol)
      (⟨32⟩ :: off :: cutoff :: stride :: slot :: len :: ptr :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorVaultLongFinishPC symbol more)
      (stride :: slot :: len :: ⟨1⟩ :: ptr :: constructorVaultEventPC symbol ::
        stringSetTopic symbol :: R) mem aw' rdata σ k' C' := by
  have hraw : ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorVaultLongFinishPC symbol more)
      (stride :: slot :: len :: ⟨1⟩ :: ptr :: constructorVaultEventPC symbol ::
        memLoad ⟨0⟩ ((metaMorphoV1_1CreationBytecode ++ tail).write
          (constructorVaultTopicOffset symbol) mem 0 32) :: R)
      (writeWord ((metaMorphoV1_1CreationBytecode ++ tail).write
        (constructorVaultTopicOffset symbol) mem 0 32) 0 (memLoad ⟨0⟩ mem)) aw' rdata σ k' C' := by
    cases symbol with
    | false =>
      cases more with
      | false => exact metaMorphoV1_1Creation_block_1910_fallthrough_packed hstack hcond rd
      | true => exact metaMorphoV1_1Creation_block_1910_taken_packed hstack hcond (by native_decide) rd
    | true =>
      cases more with
      | false => exact metaMorphoV1_1Creation_block_1653_fallthrough_packed hstack hcond rd
      | true => exact metaMorphoV1_1Creation_block_1653_taken_packed hstack hcond (by native_decide) rd
  simpa only [constructorVaultTopicRead, constructorVaultTopicRestore tail mem symbol hmem] using hraw

theorem constructorVaultLongHeaderStore {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {junk₀ junk₁ len ptr : UInt256} {R : List UInt256} (symbol : Bool)
    (hstack : R.length + 7 ≤ 1024) (hperm : I.perm = true)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultLongFinishPC symbol false)
      (junk₀ :: junk₁ :: len :: ⟨1⟩ :: ptr :: constructorVaultEventPC symbol :: stringSetTopic symbol :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultEncodePC symbol)
      (ptr :: constructorVaultEventPC symbol :: stringSetTopic symbol :: R) mem aw' rdata
      (sstoreAccountMap I.codeOwner σ (stringViewSlot symbol) (stringLongHeader len)) k' C' := by
  cases symbol with
  | false =>
    exact metaMorphoV1_1Creation_block_1942_packed
      (by simp only [List.length_cons]; omega) hperm (by native_decide) rd
  | true =>
    exact metaMorphoV1_1Creation_block_1685_packed
      (by simp only [List.length_cons]; omega) hperm (by native_decide) rd

theorem constructorVaultLongTailStore {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {stride slot len ptr : UInt256} {R : List UInt256} (symbol : Bool)
    (hstack : R.length + 11 ≤ 1024) (hperm : I.perm = true)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultLongFinishPC symbol true)
      (stride :: slot :: len :: ⟨1⟩ :: ptr :: constructorVaultEventPC symbol :: stringSetTopic symbol :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultEncodePC symbol)
      (ptr :: constructorVaultEventPC symbol :: stringSetTopic symbol :: R) mem aw' rdata
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ slot (stringStorageTailWord (memLoad (ptr + stride) mem) len))
        (stringViewSlot symbol) (stringLongHeader len)) k' C' := by
  have hnext : ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorVaultLongFinishPC symbol false)
      (⟨0⟩ :: ⟨0⟩ :: len :: ⟨1⟩ :: ptr :: constructorVaultEventPC symbol :: stringSetTopic symbol :: R)
      mem aw' rdata
      (sstoreAccountMap I.codeOwner σ slot (stringStorageTailWord (memLoad (ptr + stride) mem) len))
      k' C' := by
    cases symbol with
    | false =>
      exact metaMorphoV1_1Creation_block_1955_packed
        (by simp only [List.length_cons]; omega) hperm (by native_decide) rd
    | true =>
      exact metaMorphoV1_1Creation_block_1698_packed
        (by simp only [List.length_cons]; omega) hperm (by native_decide) rd
  obtain ⟨_, _, _, r1⟩ := hnext
  exact constructorVaultLongHeaderStore symbol (by omega) hperm r1

theorem constructorVaultDataFinish {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata bytes : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr : UInt256} (a : ConstructorArgs) (symbol : Bool)
    (hperm : I.perm = true) (buffer : StringBuffer mem ptr.toNat bytes)
    (hfit : ptr.toNat + 32 + bytes.size < UInt256.size)
    (hlong : 32 ≤ bytes.size) (hsmall : bytes.size < 2 ^ 64)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultDataExitPC symbol)
      (⟨32⟩ :: UInt256.ofNat (32 * (bytes.size / 32)) ::
        UInt256.land (UInt256.ofNat bytes.size) (UInt256.lnot ⟨31⟩) ::
        UInt256.ofNat (32 * (bytes.size / 32 + 1)) ::
        solidityBytesDataSlot (stringViewSlot symbol) (bytes.size / 32) ::
        UInt256.ofNat bytes.size :: ptr :: constructorVaultTail a symbol) mem aw rdata
      (solidityDataWordsForwardFrom I.codeOwner σ (stringViewSlot symbol) bytes 0
        (bytes.size / 32)) k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultEncodePC symbol)
      (ptr :: constructorVaultEventPC symbol :: stringSetTopic symbol :: constructorVaultTail a symbol)
      mem aw' rdata (sstoreAccountMap I.codeOwner
        (solidityDataWordsForwardFrom I.codeOwner σ (stringViewSlot symbol) bytes 0
          (solidityBytesDataWordCount bytes.size))
        (stringViewSlot symbol) (solidityBytesHeaderWord bytes.size)) k' C' := by
  have hn : (UInt256.ofNat bytes.size).toNat = bytes.size := UInt256.toNat_ofNat_of_lt (by omega)
  have hm : 32 ≤ mem.size := by have hb := buffer.size; omega
  by_cases hz : bytes.size % 32 = 0
  · obtain ⟨_, _, _, r1⟩ := constructorVaultLongPrepare symbol false
      (by cases symbol <;> simp [constructorVaultTail]) hm
      (longDataNoTail _ (by rw [hn]; exact hz)) rd
    obtain ⟨aw2, k2, C2, r2⟩ := constructorVaultLongHeaderStore symbol
      (by cases symbol <;> simp [constructorVaultTail]) hperm r1
    have hc : solidityBytesDataWordCount bytes.size = bytes.size / 32 := by
      unfold solidityBytesDataWordCount; omega
    rw [stringLongHeader_eq _ hlong] at r2
    exact ⟨aw2, k2, C2, by simpa only [hc] using r2⟩
  · have hcond : UInt256.lt (UInt256.land (UInt256.ofNat bytes.size) (UInt256.lnot ⟨31⟩))
        (UInt256.ofNat bytes.size) ≠ (⟨0⟩ : UInt256) := by
      rw [ult_one (by rw [longDataCutoff_toNat, hn]; omega)]; decide
    obtain ⟨_, _, _, r1⟩ := constructorVaultLongPrepare symbol true
      (by cases symbol <;> simp [constructorVaultTail]) hm hcond rd
    obtain ⟨aw2, k2, C2, r2⟩ := constructorVaultLongTailStore symbol
      (by cases symbol <;> simp [constructorVaultTail]) hperm r1
    rw [buffer.storageTail hfit hn hsmall hz, stringLongHeader_eq _ hlong] at r2
    have hc : solidityBytesDataWordCount bytes.size = bytes.size / 32 + 1 := by
      unfold solidityBytesDataWordCount; omega
    refine ⟨aw2, k2, C2, ?_⟩
    rw [hc, solidityDataWordsForwardFrom_append]
    simpa only [solidityDataWordsForwardFrom, Nat.zero_add] using r2

end Benchmarks.Morpho.MetaMorphoV1_1
