import Benchmarks.EAS.EAS.RecordMemory
import Benchmarks.EAS.EAS.StructEncodeViews
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def storedAttestationRecord (evm : EVM.State) (word : UInt256) : AttestationRecord :=
  let slot := dbSlot word
  let load := EVM.storageLoad evm evm.executionEnv.codeOwner
  { uid := load slot, schema := load (slot+⟨1⟩)
    time := UInt256.land (load (slot+⟨2⟩)) ⟨18446744073709551615⟩
    expirationTime := UInt256.land (UInt256.shiftRight (load (slot+⟨2⟩)) ⟨64⟩) ⟨18446744073709551615⟩
    revocationTime := UInt256.land (UInt256.shiftRight (load (slot+⟨2⟩)) ⟨128⟩) ⟨18446744073709551615⟩
    refUID := load (slot+⟨3⟩)
    recipient := AccountAddress.ofNat (UInt256.land (load (slot+⟨4⟩)) solcAddrMask).toNat
    attester := AccountAddress.ofNat (UInt256.land (load (slot+⟨5⟩)) solcAddrMask).toNat
    revocable := !(decide (UInt256.land (UInt256.shiftRight (load (slot+⟨5⟩)) ⟨160⟩) ⟨255⟩ = ⟨0⟩))
    data := attestationPayload evm word }

theorem storedAttestationRecord_value (evm : EVM.State) (word : UInt256) :
    (storedAttestationRecord evm word).value =
      attestationValue evm word (.bytes (attestationPayload evm word)) := by
  simp only [attestationValue, attestationStoredFields, storageLocLoad_bytes32,
    attestationU64_read, storageLocLoad_address_offset0, attestationBool_read, wordToElemBool,
    show (8*(0 : Fin 32).val) = 0 from rfl, wordShiftRight_zero]
  rfl

-- LIBRARY CANDIDATE: a Boolean nonzero test is the EVM's normalized Boolean word.
theorem nonzeroBool_word (word : UInt256) :
    (!(decide (word = ⟨0⟩))).toUInt256 = UInt256.isZero (UInt256.isZero word) := by
  by_cases hz : word = ⟨0⟩
  · simp only [hz, decide_true, Bool.not_true]; rfl
  · simp only [hz, decide_false, Bool.not_false, isZero_eq_zero_of_ne hz]; rfl

theorem storedAttestationRecord_words (evm : EVM.State) (word : UInt256) :
    (storedAttestationRecord evm word).words =
      storedAttestationWords evm.accountMap evm.executionEnv (dbSlot word) := by
  have ha (w : UInt256) : UInt256.ofNat (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat).val =
      UInt256.land w solcAddrMask := by
    rw [← keyValueToWord_address, keyValueToWord_address_ofNat_mask,
      u256_land_comm solcAddrMask, maskTwice]
  simp only [AttestationRecord.words, storedAttestationRecord, ha, nonzeroBool_word,
    storageLoad_eq_solcSlotWord]
  rfl

theorem copyStoredOutputMemory_preserve (evm : EVM.State) (word heap : UInt256) (mem : ByteArray)
    (hv : copyStoredValid evm word heap.toNat) :
    MemoryPrefix mem (copyStoredOutputMemory evm word heap mem) heap.toNat := by
  have hf : MemoryPrefix mem
      (copyStoredFieldsMemory mem heap evm.accountMap evm.executionEnv (dbSlot word)) heap.toNat :=
    (memoryPrefix_sparse_writeWord mem 64 heap.toNat _ (Or.inr (by decide))).trans
      (writeWordSequence_prefix _ _ _ _ (le_refl _))
  exact hf.trans ((copyStoredOutputMemory_prefix evm word heap mem hv.1).mono (by omega))

theorem copyStoredOutputMemory_view (evm : EVM.State) (word heap : UInt256) (mem : ByteArray)
    (hlo : 96 ≤ heap.toNat) (hv : copyStoredValid evm word heap.toNat) :
    AttestationMemoryView (copyStoredOutputMemory evm word heap mem) heap
      (copyStoredBytePtr heap) (storedAttestationRecord evm word) := by
  have hp := copyStoredBytePtr_nat (heap := heap) hv.1
  have hc := copyStoredOutputMemory_coversRounded evm word heap mem hv
  refine ⟨hlo, by omega, by omega, hc,
    copyStoredOutputMemory_loadDataPointer evm word heap mem hv.1,
    copyStoredOutputMemory_loadLength evm word heap mem hlo hv, ?_,
    copyStoredOutputMemory_data evm word heap mem hlo hv⟩
  rw [storedAttestationRecord_words]
  exact copyStoredOutputMemory_headWords evm word heap mem hv.1 hlo

end Benchmarks.EAS.EAS
