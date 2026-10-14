import Benchmarks.EAS.EAS.ScalarFields
import Benchmarks.EAS.EAS.AttestationStorage
import Benchmarks.EAS.EAS.EncodeAttestationSource
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def attestationWordWrite (name : Ident) (slot word : UInt256) : ScalarFieldWrite :=
  ⟨name,bytes32Loc slot,wordBytes32Value word,word,valueToWord_bytes32_word word,rfl⟩
def attestationTimeWrite (name : Ident) (slot : UInt256) (off : Fin 32) (hb : off.val+8-1 < 32) (word : UInt256) : ScalarFieldWrite :=
  ⟨name,attestationU64Loc slot off hb,.int (Int.ofNat word.toNat),word,
    by simp only [valueToWord,wordOfInt_ofNat_toNat,pure],rfl⟩
def attestationAddressWrite (name : Ident) (slot : UInt256) (addr : AccountAddress) : ScalarFieldWrite :=
  ⟨name,addressOffset0Loc slot,.address addr,UInt256.ofNat addr.val,rfl,rfl⟩

def attestationScalarWrites (slot : UInt256) (a : AttestationRecord) : List ScalarFieldWrite := [
  attestationWordWrite "uid" slot a.uid,
  attestationWordWrite "schema" (slot+⟨1⟩) a.schema,
  attestationTimeWrite "time" (slot+⟨2⟩) 0 (by decide) a.time,
  attestationTimeWrite "expirationTime" (slot+⟨2⟩) 8 (by decide) a.expirationTime,
  attestationTimeWrite "revocationTime" (slot+⟨2⟩) 16 (by decide) a.revocationTime,
  attestationWordWrite "refUID" (slot+⟨3⟩) a.refUID,
  attestationAddressWrite "recipient" (slot+⟨4⟩) a.recipient,
  attestationAddressWrite "attester" (slot+⟨5⟩) a.attester,
  ⟨"revocable",attestationBoolLoc (slot+⟨5⟩),.bool a.revocable,a.revocable.toUInt256,rfl,rfl⟩]

def attestationWriteHead (evm : EVM.State) (slot : UInt256) (a : AttestationRecord) : EVM.State :=
  writeScalarFields (attestationScalarWrites slot a) evm
def attestationWriteAccounts (σ : AccountMap) (ee : ExecutionEnv) (slot : UInt256) (a : AttestationRecord) : AccountMap :=
  writeScalarAccounts (attestationScalarWrites slot a) σ ee

theorem attestationScalarWrites_layout (word : UInt256) (a : AttestationRecord) :
    ∀ f ∈ attestationScalarWrites (dbSlot word) a,
      easStorageLayout {attestationER word with steps := (attestationER word).steps ++ [.field f.name]} = some (.leaf f.loc) := by
  intro f hf
  simp only [attestationScalarWrites,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    change some (StorageAddr.leaf _) = some (StorageAddr.leaf _)
    simp only [abiBytes32Width,keyValueToWord_fixedBytes32]
    rfl

theorem attestation_writeFields (evm : EVM.State) (word : UInt256) (a : AttestationRecord) :
    config.storageBackend.write (attestationER word) attestationType a.value evm =
      config.storageBackend.write (attestationFieldER word "data") .bytes (.bytes a.data)
        (attestationWriteHead evm (dbSlot word) a) := by
  rw [easStorageBackend]
  simp only [solidityStorageBackend,attestationType,AttestationRecord.value,solidityWriteStorage?,if_pos rfl]
  change solidityWriteFields? easStorageLayout evm (attestationER word)
    (scalarFieldTypes (attestationScalarWrites (dbSlot word) a) ++ [("data",.bytes)])
    (scalarFieldValues (attestationScalarWrites (dbSlot word) a) ++ [("data",.bytes a.data)]) = _
  rw [solidityWriteFields_scalarPrefix _ _ _ _ _ _ (attestationScalarWrites_layout word a)]
  rw [solidityWriteFields?,if_pos rfl]
  change (solidityWriteStorage? easStorageLayout (attestationWriteHead evm (dbSlot word) a)
      (attestationFieldER word "data") .bytes (.bytes a.data)).bind
      (fun e => solidityWriteFields? easStorageLayout e (attestationER word) [] []) = _
  cases h : solidityWriteStorage? easStorageLayout (attestationWriteHead evm (dbSlot word) a)
      (attestationFieldER word "data") .bytes (.bytes a.data)
  all_goals
    simp only [solidityWriteStorage?] at h
    simpa only [EvalResult.bind,solidityWriteFields?] using h.symm

theorem attestationWriteHead_sourceState {s0 ee σ evm} (hs : SourceState s0 ee σ evm) (slot : UInt256) (a : AttestationRecord) :
    SourceState s0 ee (attestationWriteAccounts σ ee slot a) (attestationWriteHead evm slot a) :=
  writeScalarFields_sourceState hs _

end Benchmarks.EAS.EAS
