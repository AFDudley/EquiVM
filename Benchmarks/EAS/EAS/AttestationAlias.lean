import Benchmarks.EAS.EAS.StoredRecord
import Benchmarks.EAS.EAS.AttestationWriteStatements
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def attestationAliasRef (field : Ident) : StorageRef := {base := "attestation",steps := [.field field]}

theorem attestationRoot_resolve {evm : EVM.State} {L imms : Store} {word : UInt256} {expr : Expr}
    (hnone : L.get? "_db" = none)
    (he : evalExpr? config {contract := contract,locals := L,immutables := imms} evm expr = .ok (wordBytes32Value word)) :
    resolveStorageRef? config {contract := contract,locals := L,immutables := imms} evm
      {base := "_db",steps := [.mindex expr]} = .ok (attestationER word,attestationType) := by
  apply resolveStorageRef?_ok (ty := attestationType) hnone
  · have hlen : (EVM.Word.toBytesBE word).length = 32 := by simpa using word_toBytesBE_toByteArray_size word
    simp only [evalStorageRef,evalStorageRefSteps,evalStorageRefStep,he,wordBytes32Value,EvalResult.ofOption,
      valueToKey?,hlen,abiBytes32Width,show (31 : Nat)+1 = 32 from rfl,if_true,pure,bind,EvalResult.bind]
    rfl
  · rfl

theorem attestationAlias_resolve {evm : EVM.State} {L imms : Store} {word : UInt256} {field : Ident} {ty : StorageType}
    (ha : L.get? "attestation" = some (.storageRef (attestationER word) attestationType))
    (ht : storageTypeStep? attestationType (.field field) = some ty) :
    resolveStorageRef? config {contract := contract,locals := L,immutables := imms} evm (attestationAliasRef field) =
      .ok (attestationFieldER word field,ty) := by
  simp only [resolveStorageRef?,attestationAliasRef,ha,evalStorageRefFrom?,evalStorageRefStep,ht,
    EvalResult.ofOption,pure,bind,EvalResult.bind]
  rfl

theorem attestationScalarWrites_fieldType (slot : UInt256) (a : AttestationRecord) :
    ∀ f ∈ attestationScalarWrites slot a,
      storageTypeStep? attestationType (.field f.name) = some (.elem f.loc.type) := by
  intro f hf
  simp only [attestationScalarWrites,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem storedAttestationRecord_scalar (evm : EVM.State) (word : UInt256) :
    ∀ f ∈ attestationScalarWrites (dbSlot word) (storedAttestationRecord evm word),
      storageLocLoad evm f.loc = f.value := by
  intro f hf
  simp only [attestationScalarWrites,List.mem_cons,List.not_mem_nil,or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [attestationWordWrite,attestationTimeWrite,attestationAddressWrite,
    storageLocLoad_bytes32,attestationU64_read,storageLocLoad_address_offset0,attestationBool_read,
    wordToElemBool,show (8*(0 : Fin 32).val) = 0 from rfl,wordShiftRight_zero]
  all_goals rfl

theorem attestationAlias_scalar {evm : EVM.State} {L imms : Store} {word : UInt256} {f : ScalarFieldWrite}
    (ha : L.get? "attestation" = some (.storageRef (attestationER word) attestationType))
    (hf : f ∈ attestationScalarWrites (dbSlot word) (storedAttestationRecord evm word)) :
    evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.storage (attestationAliasRef f.name)) = .ok f.value := by
  exact evalExpr_storage_resolved_value
    (attestationAlias_resolve ha (attestationScalarWrites_fieldType _ _ _ hf)) easStorageBackend
    (attestationScalarWrites_layout _ _ _ hf) (storedAttestationRecord_scalar _ _ _ hf)

def revokeTimeField (word time : UInt256) : ScalarFieldWrite :=
  attestationTimeWrite "revocationTime" (dbSlot word+⟨2⟩) 16 (by decide) time

theorem attestationAlias_writeTime {evm : EVM.State} {L imms : Store} {word time : UInt256}
    (ha : L.get? "attestation" = some (.storageRef (attestationER word) attestationType)) :
    assignStorageRef? config {contract := contract,locals := L,immutables := imms} evm
      .storage (attestationAliasRef "revocationTime") (.int (Int.ofNat time.toNat)) =
      .ok ({contract := contract,locals := L,immutables := imms},(revokeTimeField word time).apply evm) := by
  apply assignStorageRef_resolved_value (attestationAlias_resolve ha (ty := .elem (.int (.uint ⟨64,by decide⟩))) rfl)
    easStorageBackend (loc := attestationU64Loc (dbSlot word+⟨2⟩) 16 (by decide))
  · change some (StorageAddr.leaf _) = some (StorageAddr.leaf _)
    simp only [abiBytes32Width,keyValueToWord_fixedBytes32]
    rfl
  · exact Or.inl ⟨_,rfl⟩
  · exact storageLocStore_packedSlice evm _ _ time rfl (by simp only [valueToWord,wordOfInt_ofNat_toNat,pure])

end Benchmarks.EAS.EAS
