import Benchmarks.EAS.EAS.CopyStoredMemory
import Benchmarks.EAS.EAS.ByteViews
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem copyStoredPayloadMemory_afterLength (mem : ByteArray) (bytesPtr slot header : UInt256) (σ : AccountMap) (ee : ExecutionEnv) :
    MemoryPrefix (Reasoning.Theory.writeWord mem bytesPtr.toNat (storedBytesLengthWord header))
      (copyStoredPayloadMemory mem bytesPtr slot header σ ee) (bytesPtr.toNat + 32) := by
  unfold copyStoredPayloadMemory
  split
  · exact memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (le_refl _))
  · exact (memoryPrefix_sparse_writeWord _ 0 _ _ (Or.inr (by decide))).trans
      (writeWordSequence_prefix _ _ _ _ (le_refl _))

theorem copyStoredPayloadMemory_length (mem : ByteArray) (bytesPtr slot header : UInt256) (σ : AccountMap) (ee : ExecutionEnv)
    (hlo : 96 ≤ bytesPtr.toNat) :
    (copyStoredPayloadMemory mem bytesPtr slot header σ ee).readWithPadding bytesPtr.toNat 32 =
      (storedBytesLengthWord header).toByteArray := by
  rw [(copyStoredPayloadMemory_afterLength mem bytesPtr slot header σ ee).read _ hlo (le_refl _)
    (by rw [writeWord_sparse_size]; omega), writeWord_sparse_read_back]

theorem copyStoredPayloadMemory_read (evm : EVM.State) (mem : ByteArray) (bytesPtr slot header : UInt256)
    (hheader : header = EVM.storageLoad evm evm.executionEnv.codeOwner slot)
    (hv : storedBytesValid header) :
    (copyStoredPayloadMemory mem bytesPtr slot header evm.accountMap evm.executionEnv).readWithPadding
      (bytesPtr.toNat + 32) (storedBytesLengthWord header).toNat =
      storedBytesPayload evm slot (storedBytesLengthWord header).toNat := by
  subst header
  let header := EVM.storageLoad evm evm.executionEnv.codeOwner slot
  let len := (storedBytesLengthWord header).toNat
  change (copyStoredPayloadMemory mem bytesPtr slot header evm.accountMap evm.executionEnv).readWithPadding
    (bytesPtr.toNat + 32) len = storedBytesPayload evm slot len
  by_cases hf : UInt256.land header ⟨1⟩ = ⟨0⟩
  · have hl : len < 32 := storedBytesValid_short hf hv
    rw [copyStoredPayloadMemory, if_pos hf, storedBytesPayload, if_pos hl]
    by_cases hz : len = 0
    · rw [hz, byteArray_readWithPadding_zero]
      exact (byteArray_extract_empty_of_le _ (by omega)).symm
    · have hp : 0 < len := by omega
      have hw := writeWord_sparse_read_window
        (Reasoning.Theory.writeWord mem bytesPtr.toNat (storedBytesLengthWord header)) (bytesPtr.toNat + 32)
        0 len (UInt256.land (UInt256.lnot ⟨255⟩) header) (by omega) hp (by omega)
      simpa only [Nat.add_zero, Nat.zero_add, clearLowByte_prefix header len (by omega)] using hw
  · have hl : ¬ len < 32 := Nat.not_lt.mpr (storedBytesValid_long hf hv)
    rw [copyStoredPayloadMemory, if_neg hf, storedBytesPayload, if_neg hl,
      writeWordSequence_read_prefix _ _ _ len (by rw [storedWords_length]; dsimp only [len]; omega), storedWords_solidityBytes]
    rfl

theorem copyStoredPayloadMemory_covers (mem : ByteArray) (bytesPtr slot header : UInt256) (σ : AccountMap) (ee : ExecutionEnv)
    (hv : storedBytesValid header) :
    bytesPtr.toNat + 32 + (storedBytesLengthWord header).toNat ≤
      (copyStoredPayloadMemory mem bytesPtr slot header σ ee).size := by
  unfold copyStoredPayloadMemory
  split
  next hf =>
    have hl := storedBytesValid_short hf hv
    rw [writeWord_sparse_size]
    omega
  next hf =>
    have hl := storedBytesValid_long hf hv
    have hn : (storedBytesLengthWord header).toNat ≤
        32 * (((storedBytesLengthWord header).toNat + 31) / 32) := by omega
    have hc := writeWordSequence_covers
      (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem bytesPtr.toNat
        (storedBytesLengthWord header)) 0 slot)
      (bytesPtr.toNat + 32)
      (storedWords σ ee (solidityBytesDataSlot slot 0)
        (((storedBytesLengthWord header).toNat + 31) / 32))
      (by intro he; have he' := congrArg List.length he; rw [storedWords_length] at he'; simp only [List.length_nil] at he'; omega)
    rw [storedWords_length] at hc
    exact le_trans (by omega) hc

-- LIBRARY CANDIDATE: any finite byte window above a word write is preserved, including the empty window.
theorem writeWord_read_above (mem : ByteArray) (off read len : Nat) (word : UInt256)
    (hlo : off + 32 ≤ read) (hin : read + len ≤ mem.size) (hlen : len < 2^64) :
    (Reasoning.Theory.writeWord mem off word).readWithPadding read len = mem.readWithPadding read len := by
  by_cases hz : len = 0
  · simp only [hz, byteArray_readWithPadding_zero]
  · exact writeWord_read_preserved_len mem off read len word
      (by
        have h : off ≤ mem.size := by omega
        rw [Nat.sub_eq_zero_of_le h]
        exact lt_usize 0 (by decide))
      (Or.inr ⟨hlo, hin⟩) (by omega) hlen

theorem copyStoredOutputMemory_data (evm : EVM.State) (word heap : UInt256) (mem : ByteArray)
    (hlo : 96 ≤ heap.toNat) (hv : copyStoredValid evm word heap.toNat) :
    (copyStoredOutputMemory evm word heap mem).readWithPadding ((copyStoredBytePtr heap).toNat + 32)
      (attestationPayload evm word).size = attestationPayload evm word := by
  have hb := copyStoredBytePtr_nat (heap := heap) hv.1
  have hc := copyStoredPayloadMemory_covers
    (copyStoredFieldsMemory mem heap evm.accountMap evm.executionEnv (dbSlot word))
    (copyStoredBytePtr heap) (dbSlot word + ⟨6⟩) (attestationHeader evm word) evm.accountMap evm.executionEnv hv.2.1
  have hl := (copyStoredValid_size evm word heap.toNat hv).2
  have hs := attestationPayload_size evm word
  change (copyStoredBytePtr heap).toNat + 32 + (storedBytesLengthWord (attestationHeader evm word)).toNat ≤ _ at hc
  rw [← hs] at hc
  rw [copyStoredOutputMemory,
    writeWord_read_above _ (heap.toNat + 288) _ _ _ (by omega)
      (by rw [writeWord_sparse_size]; omega) hl,
    writeWord_read_above _ 64 _ _ _ (by omega) hc hl, hs]
  have hheader : attestationHeader evm word = EVM.storageLoad evm evm.executionEnv.codeOwner (dbSlot word + ⟨6⟩) := by rfl
  have hgood : storedBytesValid (attestationHeader evm word) := hv.2.1
  exact copyStoredPayloadMemory_read evm
    (copyStoredFieldsMemory mem heap evm.accountMap evm.executionEnv (dbSlot word))
    (copyStoredBytePtr heap) (dbSlot word + (⟨6⟩ : UInt256)) (attestationHeader evm word) hheader hgood


theorem copyStoredPayloadMemory_coversRounded (mem : ByteArray) (bytesPtr slot header : UInt256) (σ : AccountMap) (ee : ExecutionEnv)
    (hv : storedBytesValid header) :
    bytesPtr.toNat + 32 + 32 * (((storedBytesLengthWord header).toNat + 31) / 32) ≤
      (copyStoredPayloadMemory mem bytesPtr slot header σ ee).size := by
  unfold copyStoredPayloadMemory
  split
  next hf =>
    have hl := storedBytesValid_short hf hv
    rw [writeWord_sparse_size]
    omega
  next hf =>
    have hl := storedBytesValid_long hf hv
    have hc := writeWordSequence_covers
      (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem bytesPtr.toNat (storedBytesLengthWord header)) 0 slot)
      (bytesPtr.toNat + 32)
      (storedWords σ ee (solidityBytesDataSlot slot 0) (((storedBytesLengthWord header).toNat + 31) / 32))
      (by
        intro he
        have he' := congrArg List.length he
        rw [storedWords_length] at he'
        simp only [List.length_nil] at he'
        omega)
    rw [storedWords_length] at hc
    exact hc

theorem copyStoredOutputMemory_coversRounded (evm : EVM.State) (word heap : UInt256) (mem : ByteArray)
    (hv : copyStoredValid evm word heap.toNat) :
    (copyStoredBytePtr heap).toNat + 32 + 32 * (((attestationPayload evm word).size + 31) / 32) ≤
      (copyStoredOutputMemory evm word heap mem).size := by
  have hc := copyStoredPayloadMemory_coversRounded
    (copyStoredFieldsMemory mem heap evm.accountMap evm.executionEnv (dbSlot word))
    (copyStoredBytePtr heap) (dbSlot word + (⟨6⟩ : UInt256)) (attestationHeader evm word) evm.accountMap evm.executionEnv hv.2.1
  rw [copyStoredOutputMemory, writeWord_sparse_size, writeWord_sparse_size, attestationPayload_size]
  exact le_trans hc (by omega)

theorem copyStoredOutputMemory_covers (evm : EVM.State) (word heap : UInt256) (mem : ByteArray)
    (hv : copyStoredValid evm word heap.toNat) :
    (copyStoredBytePtr heap).toNat + 32 + (attestationPayload evm word).size ≤
      (copyStoredOutputMemory evm word heap mem).size := by
  have hc := copyStoredPayloadMemory_covers
    (copyStoredFieldsMemory mem heap evm.accountMap evm.executionEnv (dbSlot word))
    (copyStoredBytePtr heap) (dbSlot word + (⟨6⟩ : UInt256)) (attestationHeader evm word) evm.accountMap evm.executionEnv hv.2.1
  rw [copyStoredOutputMemory, writeWord_sparse_size, writeWord_sparse_size, attestationPayload_size]
  exact le_trans hc (by omega)

theorem copyStoredOutputMemory_length (evm : EVM.State) (word heap : UInt256) (mem : ByteArray)
    (hlo : 96 ≤ heap.toNat) (hv : copyStoredValid evm word heap.toNat) :
    (copyStoredOutputMemory evm word heap mem).readWithPadding (copyStoredBytePtr heap).toNat 32 =
      (storedBytesLengthWord (attestationHeader evm word)).toByteArray := by
  have hb := copyStoredBytePtr_nat (heap := heap) hv.1
  have hc := copyStoredPayloadMemory_covers
    (copyStoredFieldsMemory mem heap evm.accountMap evm.executionEnv (dbSlot word))
    (copyStoredBytePtr heap) (dbSlot word + (⟨6⟩ : UInt256)) (attestationHeader evm word) evm.accountMap evm.executionEnv hv.2.1
  rw [copyStoredOutputMemory,
    writeWord_sparse_read_preserved _ _ _ _ (Or.inr ⟨by omega, by rw [writeWord_sparse_size]; omega⟩),
    writeWord_sparse_read_preserved _ _ _ _ (Or.inr ⟨by omega, by omega⟩)]
  exact copyStoredPayloadMemory_length _ _ _ _ _ _ (by omega)

theorem copyStoredOutputMemory_loadLength (evm : EVM.State) (word heap : UInt256) (mem : ByteArray)
    (hlo : 96 ≤ heap.toNat) (hv : copyStoredValid evm word heap.toNat) :
    memLoad (copyStoredBytePtr heap) (copyStoredOutputMemory evm word heap mem) =
      UInt256.ofNat (attestationPayload evm word).size := by
  rw [attestationPayload_size, u256_ofNat_toNat]
  exact mloadWordValue_of_readWithPadding (by have hc := copyStoredOutputMemory_covers evm word heap mem hv; omega)
    (copyStoredOutputMemory_length evm word heap mem hlo hv)

end Benchmarks.EAS.EAS
