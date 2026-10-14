import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDomainContext

/-! Preserve the decoded vault name and symbol through the constructor's domain writes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] ConstructorArgs.encoded
set_option autoImplicit false

-- LIBRARY CANDIDATE: a word sequence preserves a complete byte buffer below its first store.
theorem SourceMemory.BytesBuffer.wordSequence_before {mem bytes : ByteArray} {ptr : UInt256}
    (buffer : BytesBuffer mem ptr bytes) (off : Nat) (words : List UInt256)
    (hbelow : ptr.toNat + 32 + bytes.size ≤ off) :
    BytesBuffer (wordSequenceMemory mem off words) ptr bytes := by
  induction words generalizing off mem with
  | nil => exact buffer
  | cons word words ih =>
    exact ih (buffer.writeWord off word (.inl hbelow)) (off + 32) (by omega)

theorem constructorDomainConstantsMemory_buffer {mem bytes : ByteArray} {ptr : UInt256}
    (buffer : BytesBuffer mem ptr bytes) (hlo : 416 ≤ ptr.toNat) :
    BytesBuffer (constructorDomainConstantsMemory mem) ptr bytes :=
  (((buffer.writeWord 384 _ (.inr hlo)).writeWord 288 _ (.inr (by omega))).writeWord
    320 _ (.inr (by omega))).writeWord 224 _ (.inr (by omega))

theorem constructorDomainCachedMemory_buffer {mem bytes : ByteArray} {ptr : UInt256}
    (buffer : BytesBuffer mem ptr bytes) (I : ExecutionEnv) (free : Nat)
    (hlo : 416 ≤ ptr.toNat) (hbelow : ptr.toNat + 32 + bytes.size ≤ free) :
    BytesBuffer (constructorDomainCachedMemory mem I free) ptr bytes := by
  have hb := constructorDomainConstantsMemory_buffer buffer hlo
  have hw := hb.wordSequence_before (free + 32) (constructorDomainWords I) (by omega)
  have hl := hw.writeWord free (UInt256.ofNat (32 * (constructorDomainWords I).length)) (.inl hbelow)
  have hf := hl.writeWord 64 (UInt256.ofNat (free + 32 + 32 * (constructorDomainWords I).length))
    (.inr (by omega))
  exact (hf.writeWord 192 (constructorDomainHash I) (.inr (by omega))).writeWord
    256 (UInt256.ofNat I.codeOwner.val) (.inr (by omega))

theorem constructorDomainReadyMemory_buffers (mem : ByteArray) (a : ConstructorArgs)
    (ok : Bool) (out : ByteArray) (I : ExecutionEnv)
    (hbound : 23666 + a.encoded.length < UInt256.size)
    (hsmall : a.argumentEnd < 2 ^ 64) (hname : a.nameEnd < 2 ^ 64)
    (hcursor : a.stringsEnd ≤ (constructorDecimalsCursor a out).toNat)
    (hp : ByteMemoryPrefix (constructorVersionMemory (constructorStringsMemory a) a.stringsEnd)
      mem (a.stringsEnd + 160)) :
    BytesBuffer (constructorDomainReadyMemory mem a ok out I) (UInt256.ofNat a.argumentEnd) a.name ∧
    BytesBuffer (constructorDomainReadyMemory mem a ok out I) (UInt256.ofNat a.nameEnd) a.symbol := by
  have hnword : a.argumentEnd < UInt256.size := by change a.argumentEnd < 2 ^ 256; omega
  have hsword : a.nameEnd < UInt256.size := by change a.nameEnd < 2 ^ 256; omega
  have hnsize : a.name.size ≤ paddedSize a.name.size := by unfold paddedSize; omega
  have hssize : a.symbol.size ≤ paddedSize a.symbol.size := by unfold paddedSize; omega
  have hnlo : 480 ≤ a.argumentEnd := by unfold ConstructorArgs.argumentEnd; omega
  have hslo : 480 ≤ a.nameEnd := by unfold ConstructorArgs.nameEnd; omega
  have hnhi : a.argumentEnd + 32 + a.name.size ≤ a.stringsEnd := by
    unfold ConstructorArgs.stringsEnd ConstructorArgs.nameEnd
    omega
  have hshi : a.nameEnd + 32 + a.symbol.size ≤ a.stringsEnd := by
    unfold ConstructorArgs.stringsEnd
    omega
  have hprefix := (constructorVersionMemory_prefix (constructorStringsMemory a) a.stringsEnd).trans
    (hp.mono (by omega))
  have hn := (constructorStringsMemory_name a hbound hsmall).preserve hprefix
    (by rw [UInt256.toNat_ofNat_of_lt hnword]; omega)
    (by rw [UInt256.toNat_ofNat_of_lt hnword]; exact hnhi)
  have hs := (constructorStringsMemory_symbol a hbound hsmall hname).preserve hprefix
    (by rw [UInt256.toNat_ofNat_of_lt hsword]; omega)
    (by rw [UInt256.toNat_ofNat_of_lt hsword]; exact hshi)
  refine ⟨constructorDomainCachedMemory_buffer (constructorAssetReadyMemory_buffer a ok out hn
    (by rw [UInt256.toNat_ofNat_of_lt hnword]; omega)) I (constructorDecimalsCursor a out).toNat
    (by rw [UInt256.toNat_ofNat_of_lt hnword]; omega)
    (by rw [UInt256.toNat_ofNat_of_lt hnword]; omega), ?_⟩
  exact constructorDomainCachedMemory_buffer (constructorAssetReadyMemory_buffer a ok out hs
    (by rw [UInt256.toNat_ofNat_of_lt hsword]; omega)) I (constructorDecimalsCursor a out).toNat
    (by rw [UInt256.toNat_ofNat_of_lt hsword]; omega)
    (by rw [UInt256.toNat_ofNat_of_lt hsword]; omega)

end Benchmarks.Morpho.MetaMorphoV1_1
