import Benchmarks.EAS.EAS.BytesLength
import Benchmarks.EAS.EAS.AttestationStorage
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: exact byte payload read from Solidity's short/long storage encoding.
def storedBytesPayload (evm : EVM.State) (slot : UInt256) (len : Nat) : ByteArray :=
  if len < 32 then (EVM.storageLoad evm evm.executionEnv.codeOwner slot).toByteArray.extract 0 len
  else (readSolidityBytesDataWordsFrom evm slot 0 (solidityBytesDataWordCount len)).extract 0 len

theorem storedBytesPayload_size (evm : EVM.State) (slot : UInt256) (len : Nat) :
    (storedBytesPayload evm slot len).size = len := by
  by_cases hl : len < 32
  · simp [storedBytesPayload, hl, ByteArray.size_extract, Nat.le_of_lt hl]
  · have hcover : len ≤ 32 * solidityBytesDataWordCount len := by
      unfold solidityBytesDataWordCount
      omega
    simp [storedBytesPayload, hl, ByteArray.size_extract, hcover]

theorem storedBytesRead {cfg : Config} {layout : StorageLayout} {evm : EVM.State}
    {er : EvaledStorageRef} {slot : UInt256}
    (hcfg : cfg.storageBackend = solidityStorageBackend layout)
    (hloc : layout er = some (.anchor slot)) :
    cfg.storageBackend.read er .bytes evm =
      if storedBytesValid (EVM.storageLoad evm evm.executionEnv.codeOwner slot) then
        .ok (.bytes (storedBytesPayload evm slot (storedBytesLengthWord (EVM.storageLoad evm evm.executionEnv.codeOwner slot)).toNat))
      else .revert := by
  simp only [hcfg, solidityStorageBackend, solidityReadStorage?, solidityReadBytesValue?,
    solidityBytesBaseSlotAndLength?, solidityAnchor?, hloc, storedBytesDecode]
  by_cases hv : storedBytesValid (EVM.storageLoad evm evm.executionEnv.codeOwner slot)
  · simp only [if_pos hv]
    unfold storedBytesPayload
    split <;> rfl
  · simp only [if_neg hv, solidityValueResultToEval]

def attestationHeader (evm : EVM.State) (word : UInt256) : UInt256 :=
  EVM.storageLoad evm evm.executionEnv.codeOwner (dbSlot word + ⟨6⟩)

def attestationPayload (evm : EVM.State) (word : UInt256) : ByteArray :=
  storedBytesPayload evm (dbSlot word + ⟨6⟩) (storedBytesLengthWord (attestationHeader evm word)).toNat

theorem attestation_read {evm : EVM.State} {locals imms : Store} {word : UInt256}
    (hnone : locals.get? "_db" = none)
    (hkey : locals.get? "uid" = some (wordBytes32Value word)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm (.storage attestationRef) =
      if storedBytesValid (attestationHeader evm word) then .ok (attestationValue evm word (.bytes (attestationPayload evm word))) else .revert := by
  rw [evalExpr?, attestation_resolve hnone hkey]
  simp only [bind, EvalResult.bind, attestation_readFields, storedBytesRead easStorageBackend (attestation_data_layout word)]
  by_cases hv : storedBytesValid (attestationHeader evm word)
  · simp only [show storedBytesValid (EVM.storageLoad evm evm.executionEnv.codeOwner (dbSlot word + ⟨6⟩)) from hv, if_true, hv, EvalResult.bind]
    rfl
  · simp only [show ¬ storedBytesValid (EVM.storageLoad evm evm.executionEnv.codeOwner (dbSlot word + ⟨6⟩)) from hv, if_false, hv, EvalResult.bind]

theorem attestationValue_data (evm : EVM.State) (word : UInt256) (payload : Value) :
    lookupField? (attestationValue evm word payload) "data" = some payload := by rfl

end Benchmarks.EAS.EAS
