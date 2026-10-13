import Benchmarks.EAS.EAS.CopyStoredEVM
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem copyStoredPayloadMemory_prefix (mem : ByteArray) (bytesPtr slot header : UInt256) (σ : AccountMap) (ee : ExecutionEnv) :
    MemoryPrefix mem (copyStoredPayloadMemory mem bytesPtr slot header σ ee) bytesPtr.toNat := by
  have hp := memoryPrefix_sparse_writeWord mem bytesPtr.toNat bytesPtr.toNat (storedBytesLengthWord header) (Or.inl (le_refl _))
  unfold copyStoredPayloadMemory
  split
  · exact hp.trans (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega)))
  · exact hp.trans ((memoryPrefix_sparse_writeWord _ 0 bytesPtr.toNat slot (Or.inr (by decide))).trans
      (writeWordSequence_prefix _ _ _ _ (by omega)))

theorem copyStoredBytePtr_nat {heap : UInt256}
    (hg : allocateNext heap.toNat 320 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 320) :
    (copyStoredBytePtr heap).toNat = heap.toNat + 320 := by
  rw [copyStoredBytePtr, ulit_toNat' _ (by have hb := hg.1; change allocateNext heap.toNat 320 < 2^256; omega)]
  exact (allocate320_bounds hg).1

theorem copyStoredOutputMemory_prefix (evm : EVM.State) (word heap : UInt256) (mem : ByteArray)
    (hg : allocateNext heap.toNat 320 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 320) :
    MemoryPrefix (copyStoredFieldsMemory mem heap evm.accountMap evm.executionEnv (dbSlot word))
      (copyStoredOutputMemory evm word heap mem) (heap.toNat + 288) := by
  have hp := (copyStoredPayloadMemory_prefix
    (copyStoredFieldsMemory mem heap evm.accountMap evm.executionEnv (dbSlot word))
    (copyStoredBytePtr heap) (dbSlot word + ⟨6⟩) (attestationHeader evm word) evm.accountMap evm.executionEnv).mono
      (show heap.toNat + 288 ≤ (copyStoredBytePtr heap).toNat by rw [copyStoredBytePtr_nat hg]; omega)
  exact hp.trans ((memoryPrefix_sparse_writeWord _ 64 _ _ (Or.inr (by decide))).trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (le_refl _))))

theorem copyStoredOutputMemory_heap (evm : EVM.State) (word heap : UInt256) (mem : ByteArray) (hlo : 96 ≤ heap.toNat) :
    memLoad (UInt256.ofNat 64) (copyStoredOutputMemory evm word heap mem) =
      UInt256.ofNat (copyStoredNext heap.toNat (attestationPayload evm word)) :=
  writeWordSequence_setFree_load64 _ (heap.toNat + 288) [copyStoredBytePtr heap] _ (by omega)

theorem copyStoredOutputMemory_field (evm : EVM.State) (word heap : UInt256) (mem : ByteArray)
    (hg : allocateNext heap.toNat 320 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 320)
    (hlo : 96 ≤ heap.toNat) (i : Nat) (hi : i < 9) :
    (copyStoredOutputMemory evm word heap mem).readWithPadding (heap.toNat + 32*i) 32 =
      ((storedAttestationWords evm.accountMap evm.executionEnv (dbSlot word))[i]'(by simpa only [storedAttestationWords, List.length_cons, List.length_nil] using hi)).toByteArray := by
  have hn : (storedAttestationWords evm.accountMap evm.executionEnv (dbSlot word)).length = 9 := rfl
  have hc := writeWordSequence_covers
    (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat 320))) heap.toNat
    (storedAttestationWords evm.accountMap evm.executionEnv (dbSlot word)) (by intro he; have hx := congrArg List.length he; rw [hn] at hx; contradiction)
  rw [hn] at hc
  rw [(copyStoredOutputMemory_prefix evm word heap mem hg).read _ (by omega) (by omega) (by exact le_trans (by omega) hc)]
  exact writeWordSequence_read_index _ _ _ i (by rw [hn]; exact hi)

theorem copyStoredOutputMemory_dataPointer (evm : EVM.State) (word heap : UInt256) (mem : ByteArray) :
    (copyStoredOutputMemory evm word heap mem).readWithPadding (heap.toNat + 288) 32 =
      (copyStoredBytePtr heap).toByteArray := writeWord_sparse_read_back _ _ _

-- LIBRARY CANDIDATE: the dynamic-byte allocation size is already word aligned.
theorem bytesAllocation_rounded {len : Nat} (hl : len < 2^255) :
    allocateRounded (bytesAllocation len) = bytesAllocation len := by
  rw [allocateRounded, Nat.mod_eq_of_lt (bytesAllocation_lt hl)]
  unfold bytesAllocation
  omega

theorem copyStoredNext_eq (evm : EVM.State) (word : UInt256) (heap : Nat)
    (hg : allocateNext heap 320 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 320) :
    copyStoredNext heap (attestationPayload evm word) =
      heap + 320 + bytesAllocation (storedBytesLengthWord (attestationHeader evm word)).toNat := by
  have hl := storedBytesLength_bound (attestationHeader evm word)
  rw [copyStoredNext, attestationPayload_size, (allocate320_bounds hg).1, allocateNext, bytesAllocation_rounded hl]
  apply Nat.mod_eq_of_lt
  have hh := (allocate320_bounds hg).2
  have hs : bytesAllocation (storedBytesLengthWord (attestationHeader evm word)).toNat ≤
      (storedBytesLengthWord (attestationHeader evm word)).toNat + 63 := by unfold bytesAllocation; omega
  change heap + 320 + bytesAllocation (storedBytesLengthWord (attestationHeader evm word)).toNat < 2^256
  omega

theorem copyStoredValid_size (evm : EVM.State) (word : UInt256) (heap : Nat)
    (hv : copyStoredValid evm word heap) :
    heap + 320 + bytesAllocation (attestationPayload evm word).size ≤ 2^64-1 ∧
      (attestationPayload evm word).size < 2^64 := by
  have hn := hv.2.2.1
  rw [copyStoredNext_eq evm word heap hv.1, ← attestationPayload_size] at hn
  refine ⟨hn, ?_⟩
  unfold bytesAllocation at hn
  omega

end Benchmarks.EAS.EAS
