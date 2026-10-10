import Benchmarks.EAS.EAS.Storage
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def attestationFields : List (Ident × StorageType) := [
  ("uid", .elem (.bytes abiBytes32Width)), ("schema", .elem (.bytes abiBytes32Width)),
  ("time", .elem (.int (.uint ⟨64, by decide⟩))),
  ("expirationTime", .elem (.int (.uint ⟨64, by decide⟩))),
  ("revocationTime", .elem (.int (.uint ⟨64, by decide⟩))),
  ("refUID", .elem (.bytes abiBytes32Width)), ("recipient", .elem .address),
  ("attester", .elem .address), ("revocable", .elem .bool), ("data", .bytes)]

def attestationType : StorageType := .struct "Attestation" attestationFields

def attestationRef : StorageRef := {base := "_db", steps := [.mindex (.var "uid")]}
def attestationER (word : UInt256) : EvaledStorageRef :=
  {base := "_db", steps := [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word))]}
def attestationFieldER (word : UInt256) (field : Ident) : EvaledStorageRef :=
  {base := "_db", steps := [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word)), .field field]}

def attestationU64Loc (slot : UInt256) (offset : Fin 32) (hbound : offset.val + 8 - 1 < 32) : StorageLoc :=
  {slot := slot, offset := offset, size := 8, hbound := hbound, type := .int (.uint ⟨64, by decide⟩)}

def attestationBoolLoc (slot : UInt256) : StorageLoc :=
  {slot := slot, offset := 20, size := 1, hbound := by decide, type := .bool}

def attestationStoredFields (evm : EVM.State) (slot : UInt256) : List (Ident × Value) := [
  ("uid", storageLocLoad evm (bytes32Loc slot)),
  ("schema", storageLocLoad evm (bytes32Loc (slot + ⟨1⟩))),
  ("time", storageLocLoad evm (attestationU64Loc (slot + ⟨2⟩) 0 (by decide))),
  ("expirationTime", storageLocLoad evm (attestationU64Loc (slot + ⟨2⟩) 8 (by decide))),
  ("revocationTime", storageLocLoad evm (attestationU64Loc (slot + ⟨2⟩) 16 (by decide))),
  ("refUID", storageLocLoad evm (bytes32Loc (slot + ⟨3⟩))),
  ("recipient", storageLocLoad evm (addressOffset0Loc (slot + ⟨4⟩))),
  ("attester", storageLocLoad evm (addressOffset0Loc (slot + ⟨5⟩))),
  ("revocable", storageLocLoad evm (attestationBoolLoc (slot + ⟨5⟩)))]

def attestationValue (evm : EVM.State) (word : UInt256) (payload : Value) : Value :=
  .struct "Attestation" (attestationStoredFields evm (dbSlot word) ++ [("data", payload)])

theorem attestation_evalRef {evm : EVM.State} {locals imms : Store} {word : UInt256}
    (hkey : locals.get? "uid" = some (wordBytes32Value word)) :
    evalStorageRef config {contract := contract, locals := locals, immutables := imms} evm attestationRef =
      .ok (attestationER word) := by
  have hlen : (EVM.Word.toBytesBE word).length = 32 := by simpa using word_toBytesBE_toByteArray_size word
  simp only [evalStorageRef, attestationRef, evalStorageRefSteps, evalStorageRefStep,
    evalExpr?, hkey, wordBytes32Value, EvalResult.ofOption, valueToKey?, hlen, abiBytes32Width,
    show (31 : Nat) + 1 = 32 from rfl, if_true, pure, bind, EvalResult.bind]
  rfl

theorem attestation_resolve {evm : EVM.State} {locals imms : Store} {word : UInt256}
    (hnone : locals.get? "_db" = none)
    (hkey : locals.get? "uid" = some (wordBytes32Value word)) :
    resolveStorageRef? config {contract := contract, locals := locals, immutables := imms} evm attestationRef =
      .ok (attestationER word, attestationType) := by
  exact resolveStorageRef?_ok hnone (attestation_evalRef hkey) rfl

theorem attestation_data_layout (word : UInt256) :
    easStorageLayout (attestationFieldER word "data") = some (.anchor (dbSlot word + ⟨6⟩)) := by
  change some (StorageAddr.anchor (solcMappingSlot ⟨1⟩
    (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word))) + ⟨6⟩)) = _
  simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
  rfl

-- LIBRARY CANDIDATE: read a primitive struct field before continuing its remaining fields.
theorem solidityReadFields_cons_leaf {layout : StorageLayout} {evm : EVM.State}
    {er : EvaledStorageRef} {name : Ident} {t : ABI.ElemType} {rest : List (Ident × StorageType)} {loc : StorageLoc}
    (hloc : layout {er with steps := er.steps ++ [.field name]} = some (.leaf loc)) :
    solidityReadFields? layout evm er ((name, .elem t) :: rest) =
      (solidityReadFields? layout evm er rest).bind
        (fun values => .ok ((name, storageLocLoad evm loc) :: values)) := by
  rw [solidityReadFields?, solidityReadStorage?]
  simp only [solidityLeafLoc?_of_leaf hloc, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem attestation_readFields (evm : EVM.State) (word : UInt256) :
    config.storageBackend.read (attestationER word) attestationType evm =
      (config.storageBackend.read (attestationFieldER word "data") .bytes evm).bind
        (fun payload => .ok (attestationValue evm word payload)) := by
  rw [easStorageBackend]
  simp only [solidityStorageBackend]
  rw [attestationType, solidityReadStorage?]
  dsimp only [attestationFields]
  rw [solidityReadFields_cons_leaf (layout := easStorageLayout) (er := attestationER word) (name := "uid") (loc := bytes32Loc (dbSlot word))
    (by
      change some (StorageAddr.leaf (bytes32Loc (solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word)))))) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
      rfl)]
  rw [solidityReadFields_cons_leaf (layout := easStorageLayout) (er := attestationER word) (name := "schema") (loc := bytes32Loc (dbSlot word + ⟨1⟩))
    (by
      change some (StorageAddr.leaf (bytes32Loc (solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word))) + ⟨1⟩))) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
      rfl)]
  rw [solidityReadFields_cons_leaf (layout := easStorageLayout) (er := attestationER word) (name := "time") (loc := attestationU64Loc (dbSlot word + ⟨2⟩) 0 (by decide))
    (by
      change some (StorageAddr.leaf (attestationU64Loc (solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word))) + ⟨2⟩) 0 (by decide))) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
      rfl)]
  rw [solidityReadFields_cons_leaf (layout := easStorageLayout) (er := attestationER word) (name := "expirationTime") (loc := attestationU64Loc (dbSlot word + ⟨2⟩) 8 (by decide))
    (by
      change some (StorageAddr.leaf (attestationU64Loc (solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word))) + ⟨2⟩) 8 (by decide))) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
      rfl)]
  rw [solidityReadFields_cons_leaf (layout := easStorageLayout) (er := attestationER word) (name := "revocationTime") (loc := attestationU64Loc (dbSlot word + ⟨2⟩) 16 (by decide))
    (by
      change some (StorageAddr.leaf (attestationU64Loc (solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word))) + ⟨2⟩) 16 (by decide))) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
      rfl)]
  rw [solidityReadFields_cons_leaf (layout := easStorageLayout) (er := attestationER word) (name := "refUID") (loc := bytes32Loc (dbSlot word + ⟨3⟩))
    (by
      change some (StorageAddr.leaf (bytes32Loc (solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word))) + ⟨3⟩))) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
      rfl)]
  rw [solidityReadFields_cons_leaf (layout := easStorageLayout) (er := attestationER word) (name := "recipient") (loc := addressOffset0Loc (dbSlot word + ⟨4⟩))
    (by
      change some (StorageAddr.leaf (addressOffset0Loc (solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word))) + ⟨4⟩))) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
      rfl)]
  rw [solidityReadFields_cons_leaf (layout := easStorageLayout) (er := attestationER word) (name := "attester") (loc := addressOffset0Loc (dbSlot word + ⟨5⟩))
    (by
      change some (StorageAddr.leaf (addressOffset0Loc (solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word))) + ⟨5⟩))) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
      rfl)]
  rw [solidityReadFields_cons_leaf (layout := easStorageLayout) (er := attestationER word) (name := "revocable") (loc := attestationBoolLoc (dbSlot word + ⟨5⟩))
    (by
      change some (StorageAddr.leaf (attestationBoolLoc (solcMappingSlot ⟨1⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word))) + ⟨5⟩))) = _
      simp only [abiBytes32Width, keyValueToWord_fixedBytes32]
      rfl)]
  rw [solidityReadFields?, solidityReadFields?]
  rw [show {attestationER word with steps := (attestationER word).steps ++ [.field "data"]} =
    attestationFieldER word "data" from rfl]
  cases hr : solidityReadStorage? easStorageLayout evm (attestationFieldER word "data") .bytes <;> rfl

end Benchmarks.EAS.EAS
