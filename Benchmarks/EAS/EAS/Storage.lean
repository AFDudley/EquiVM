import Benchmarks.EAS.EAS.Common

/-! # EAS storage slots and source reads -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def nonceRef : StorageRef := {base := "_nonces", steps := [.mindex (.var "account")]}
def nonceSlot (a : AccountAddress) : UInt256 := solcMappingSlot ⟨0⟩ (keyValueToWord (.address a))
def nonceWord (evm : EVM.State) (a : AccountAddress) : UInt256 :=
  EVM.storageLoad evm evm.executionEnv.codeOwner (nonceSlot a)

theorem nonce_read {evm : EVM.State} {locals imms : Store} {a : AccountAddress}
    (hnone : locals.get? "_nonces" = none)
    (hkey : locals.get? "account" = some (.address a)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage nonceRef) = .ok (.int (Int.ofNat (nonceWord evm a).toNat)) := by
  refine evalExpr_storage_scalar_value
    (er := {base := "_nonces", steps := [.mindex (.address a)]})
    (t := .int (.uint ⟨256, by decide⟩)) (loc := uint256Loc (nonceSlot a)) hnone ?_ ?_ rfl ?_
    (storageLocLoad_uint256 evm (nonceSlot a))
  · simp only [evalStorageRef, nonceRef, evalStorageRefSteps, evalStorageRefStep,
      evalExpr?, hkey, EvalResult.ofOption, valueToKey?, pure, bind, EvalResult.bind]
  · rfl
  · rfl

def timestampRef : StorageRef := {base := "_timestamps", steps := [.mindex (.var "data")]}
def timestampSlot (word : UInt256) : UInt256 := solcMappingSlot ⟨2⟩ word

def easUint64Mask : UInt256 := UInt256.ofNat 18446744073709551615

def timestampWord (evm : EVM.State) (word : UInt256) : UInt256 :=
  UInt256.land (EVM.storageLoad evm evm.executionEnv.codeOwner (timestampSlot word)) easUint64Mask

def easStorageLayout : StorageLayout := solidityLayout! [contract.structs] [contract.storage]

theorem easStorageBackend : config.storageBackend = solidityStorageBackend easStorageLayout := by rfl

def timestampEvaledRef (word : UInt256) : EvaledStorageRef :=
  {base := "_timestamps", steps := [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word))]}

def timestampLoc (word : UInt256) : StorageLoc :=
  {slot := timestampSlot word, offset := 0, size := 8, hbound := by decide, type := .int (.uint ⟨64, by decide⟩)}

theorem timestamp_evalRef {evm : EVM.State} {locals imms : Store} {word : UInt256}
    (hkey : locals.get? "data" = some (wordBytes32Value word)) :
    evalStorageRef config {contract := contract, locals := locals, immutables := imms} evm timestampRef =
      .ok (timestampEvaledRef word) := by
  have hlen : (EVM.Word.toBytesBE word).length = 32 := by simpa using word_toBytesBE_toByteArray_size word
  simp only [evalStorageRef, timestampRef, evalStorageRefSteps, evalStorageRefStep,
    evalExpr?, hkey, wordBytes32Value, EvalResult.ofOption, valueToKey?, hlen, abiBytes32Width,
    show (31 : Nat) + 1 = 32 from rfl, if_true, pure, bind, EvalResult.bind]
  rfl

theorem timestamp_layout (word : UInt256) : easStorageLayout (timestampEvaledRef word) = some (.leaf (timestampLoc word)) := by
  change some (StorageAddr.leaf {
    slot := solcMappingSlot ⟨2⟩ (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word)))
    offset := 0
    size := 8
    hbound := by decide
    type := .int (.uint ⟨64, by decide⟩)}) = _
  simp only [abiBytes32Width]
  rw [keyValueToWord_fixedBytes32]
  rfl

theorem timestamp_read {evm : EVM.State} {locals imms : Store} {word : UInt256}
    (hnone : locals.get? "_timestamps" = none)
    (hkey : locals.get? "data" = some (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word))) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage timestampRef) = .ok (.int (Int.ofNat (timestampWord evm word).toNat)) := by
  exact evalExpr_storage_scalar_value (t := .int (.uint ⟨64, by decide⟩)) (loc := timestampLoc word)
    hnone (timestamp_evalRef hkey) rfl easStorageBackend (timestamp_layout word)
    (storageLocLoad_uint_offset0 evm (timestampSlot word) 8 ⟨64, by decide⟩ rfl (by decide))

-- LIBRARY CANDIDATE: bytes32 equality is word equality.
theorem wordBytesBE_beq (a b : UInt256) :
    (EVM.Word.toBytesBE a == EVM.Word.toBytesBE b) = decide (a = b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro h
    have hw := congrArg ABI.bytesToWord h
    simpa only [bytesToWord_toBytesBE] using hw
  · intro h
    rw [h]

theorem evalBytes32Ne (a b : UInt256) :
    evalBinaryOp? .ne (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE a))
      (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE b)) = .ok (.bool (decide (a ≠ b))) := by
  have hval : (Value.fixedBytes abiBytes32Width (EVM.Word.toBytesBE a) ==
      Value.fixedBytes abiBytes32Width (EVM.Word.toBytesBE b)) =
      (EVM.Word.toBytesBE a == EVM.Word.toBytesBE b) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, Value.fixedBytes.injEq, true_and]
  simp only [evalBinaryOp?, hval, wordBytesBE_beq, decide_not]

theorem wordNonzeroEncoding (word : UInt256) :
    encodeReturnValue? (.elem .bool) (.bool (decide (word ≠ ⟨0⟩))) =
      some (UInt256.isZero (UInt256.isZero word)).toByteArray := by
  by_cases h : word = ⟨0⟩
  · subst word
    exact boolFalseReturnEncoding
  · rw [isZero_eq_zero_of_ne h]
    rw [show decide (word ≠ ⟨0⟩) = true from decide_eq_true h]
    exact boolTrueReturnEncoding

def dbUIDRef : StorageRef := {base := "_db", steps := [.mindex (.var "uid"), .field "uid"]}
def dbSlot (word : UInt256) : UInt256 := solcMappingSlot ⟨1⟩ word

def dbUIDWord (evm : EVM.State) (word : UInt256) : UInt256 :=
  EVM.storageLoad evm evm.executionEnv.codeOwner (dbSlot word)

def attestationValidExpr : Expr := .binary .ne (.storage dbUIDRef)
  (.fixedBytesLit abiBytes32Width (EVM.Word.toBytesBE ⟨0⟩))

theorem dbUID_read {evm : EVM.State} {locals imms : Store} {word : UInt256}
    (hnone : locals.get? "_db" = none)
    (hkey : locals.get? "uid" = some (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word))) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage dbUIDRef) =
      .ok (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE (dbUIDWord evm word))) := by
  have hlen : (EVM.Word.toBytesBE word).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size word
  refine evalExpr_storage_scalar_value
    (er := {base := "_db", steps := [.mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word)), .field "uid"]})
    (t := .bytes abiBytes32Width) (loc := bytes32Loc (dbSlot word)) hnone ?_ ?_ rfl ?_
    (storageLocLoad_bytes32 evm (dbSlot word))
  · simp only [evalStorageRef, dbUIDRef, evalStorageRefSteps, evalStorageRefStep,
      evalExpr?, hkey, EvalResult.ofOption, valueToKey?, hlen, abiBytes32Width,
      show (31 : Nat) + 1 = 32 from rfl, if_true, pure, bind, EvalResult.bind]
  · rfl
  · change some (StorageAddr.leaf (bytes32Loc (solcMappingSlot ⟨1⟩
        (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word)))))) = _
    simp only [abiBytes32Width]
    rw [keyValueToWord_fixedBytes32]
    rfl

theorem attestationValid_eval {evm : EVM.State} {locals imms : Store} {word : UInt256}
    (hnone : locals.get? "_db" = none)
    (hkey : locals.get? "uid" = some (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word))) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      attestationValidExpr = .ok (.bool (decide (dbUIDWord evm word ≠ ⟨0⟩))) := by
  have hread := dbUID_read (evm := evm) (imms := imms) hnone hkey
  simp only [attestationValidExpr, evalExpr?, hread, pure, bind, EvalResult.bind]
  change evalBinaryOp? .ne (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE (dbUIDWord evm word)))
    (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE ⟨0⟩)) = _
  exact evalBytes32Ne _ _

def offchainRef : StorageRef :=
  {base := "_revocationsOffchain", steps := [.mindex (.var "revoker"), .mindex (.var "data")]}

def offchainSlot (revoker data : UInt256) : UInt256 :=
  solcMappingSlot (solcMappingSlot ⟨3⟩ revoker) data

def offchainWord (evm : EVM.State) (revoker : AccountAddress) (data : UInt256) : UInt256 :=
  UInt256.land (EVM.storageLoad evm evm.executionEnv.codeOwner
    (offchainSlot (keyValueToWord (.address revoker)) data)) easUint64Mask

def offchainEvaledRef (revoker : AccountAddress) (word : UInt256) : EvaledStorageRef :=
  {base := "_revocationsOffchain", steps := [.mindex (.address revoker),
    .mindex (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word))]}

def offchainLoc (revoker : AccountAddress) (word : UInt256) : StorageLoc :=
  {slot := offchainSlot (keyValueToWord (.address revoker)) word, offset := 0, size := 8,
    hbound := by decide, type := .int (.uint ⟨64, by decide⟩)}

theorem offchain_evalRef {evm : EVM.State} {locals imms : Store} {revoker : AccountAddress} {word : UInt256}
    (hwho : locals.get? "revoker" = some (.address revoker))
    (hkey : locals.get? "data" = some (wordBytes32Value word)) :
    evalStorageRef config {contract := contract, locals := locals, immutables := imms} evm offchainRef =
      .ok (offchainEvaledRef revoker word) := by
  have hlen : (EVM.Word.toBytesBE word).length = 32 := by simpa using word_toBytesBE_toByteArray_size word
  simp only [evalStorageRef, offchainRef, evalStorageRefSteps, evalStorageRefStep,
    evalExpr?, hwho, hkey, wordBytes32Value, EvalResult.ofOption, valueToKey?, hlen, abiBytes32Width,
    show (31 : Nat) + 1 = 32 from rfl, if_true, pure, bind, EvalResult.bind]
  rfl

theorem offchain_layout (revoker : AccountAddress) (word : UInt256) :
    easStorageLayout (offchainEvaledRef revoker word) = some (.leaf (offchainLoc revoker word)) := by
  change some (StorageAddr.leaf {
    slot := offchainSlot (keyValueToWord (.address revoker))
      (keyValueToWord (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word)))
    offset := 0
    size := 8
    hbound := by decide
    type := .int (.uint ⟨64, by decide⟩)}) = _
  simp only [abiBytes32Width]
  rw [keyValueToWord_fixedBytes32]
  rfl

theorem offchain_read {evm : EVM.State} {locals imms : Store} {revoker : AccountAddress} {word : UInt256}
    (hnone : locals.get? "_revocationsOffchain" = none)
    (hwho : locals.get? "revoker" = some (.address revoker))
    (hkey : locals.get? "data" = some (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE word))) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage offchainRef) = .ok (.int (Int.ofNat (offchainWord evm revoker word).toNat)) := by
  exact evalExpr_storage_scalar_value (t := .int (.uint ⟨64, by decide⟩)) (loc := offchainLoc revoker word)
    hnone (offchain_evalRef hwho hkey) rfl easStorageBackend (offchain_layout revoker word)
    (storageLocLoad_uint_offset0 evm (offchainSlot (keyValueToWord (.address revoker)) word)
      8 ⟨64, by decide⟩ rfl (by decide))

end Benchmarks.EAS.EAS
