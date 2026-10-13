import Benchmarks.CurveVault.Common

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: mapping-only paths need no Vyper array-bound checks.
theorem vyperCheckSteps_mappings (layout : StorageLayout) (bounds : VyperBounds)
    (evm : EVM.State) (base : Ident) (path : List EvaledStorageRefStep) (keys : List KeyValue) :
    vyperCheckSteps? layout bounds evm base path (keys.map .mindex) = .ok () := by
  induction keys generalizing path with
  | nil => rfl
  | cons key keys ih =>
    simpa only [List.map_cons, vyperCheckSteps?, EvalResult.bind, bind, pure] using ih (path ++ [.mindex key])

theorem vaultReadMapping (evm : EVM.State) (base : Ident) (keys : List KeyValue)
    (ty : ElemType) (slot : UInt256)
    (hloc : boundedStorage.locate? {base := base, steps := keys.map .mindex} =
      some (.leaf (vyperWordLoc slot ty))) :
    config.storageBackend.read {base := base, steps := keys.map .mindex} (.elem ty) evm =
      .ok (wordToElem ty (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) := by
  change (do
    let _ ← vyperCheckRef? boundedStorage.locate? _ evm {base := base, steps := keys.map .mindex}
    vyperReadRaw? boundedStorage.locate? _ evm {base := base, steps := keys.map .mindex} (.elem ty)) = _
  simp only [vyperCheckRef?, vyperCheckSteps_mappings, vyperReadRaw?, vyperLeafLoc?, hloc,
    EvalResult.bind, EvalResult.ofOption, pure, bind]
  exact congrArg EvalResult.ok (storageLocLoad_vyperWord evm slot ty)

theorem vaultReadScalar (evm : EVM.State) (name : Ident) (ty : ElemType) (slot : UInt256)
    (hloc : boundedStorage.locate? {base := name, steps := []} = some (.leaf (vyperWordLoc slot ty))) :
    config.storageBackend.read {base := name, steps := []} (.elem ty) evm =
      .ok (wordToElem ty (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) :=
  vaultReadMapping evm name [] ty slot hloc

theorem vaultEvalScalar (evm : EVM.State) (locals : Store) (name : Ident)
    (ty : ElemType) (slot : UInt256)
    (hbase : locals.get? name = none)
    (hty : storageTypeAt? contract.storage {base := name, steps := []} = some (.elem ty))
    (hloc : boundedStorage.locate? {base := name, steps := []} = some (.leaf (vyperWordLoc slot ty))) :
    evalExpr? config {contract := contract, locals := locals} evm
      (.storage {base := name, steps := []}) =
      .ok (wordToElem ty (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)) := by
  apply evalExpr_storage_scalar_of_read (er := {base := name, steps := []}) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]) hty
  exact vaultReadScalar evm name ty slot hloc

theorem vaultAssignScalarUint256 (evm : State) (locals : Store) (name : Ident)
    (slot value : UInt256) (hbase : locals.get? name = none)
    (hty : storageTypeAt? contract.storage {base := name, steps := []} = some (.elem (.int (.uint ⟨256, by decide⟩))))
    (hloc : boundedStorage.locate? {base := name, steps := []} = some (.leaf (uint256Loc slot)))
    (hname : name ≠ "_controller") :
    assignStorageRef? config {contract := contract, locals := locals} evm .storage
      {base := name, steps := []} (.int (Int.ofNat value.toNat)) =
      .ok ({contract := contract, locals := locals}, Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot value) := by
  apply assignStorageRef_storage_of_write (er := {base := name, steps := []}) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]) hty
  have hbackend : config.storageBackend.write {base := name, steps := []}
      (.elem (.int (.uint ⟨256, by decide⟩))) (.int (Int.ofNat value.toNat)) evm =
      boundedStorage.write {base := name, steps := []} (.elem (.int (.uint ⟨256, by decide⟩)))
        (.int (Int.ofNat value.toNat)) evm := by
    simp only [config, storageBackend, show (name == "_controller") = false from beq_eq_false_iff_ne.mpr hname,
      Bool.false_and, Bool.false_eq_true, if_false]
  rw [hbackend]
  change (do
    let _ ← vyperCheckRef? boundedStorage.locate? _ evm {base := name, steps := []}
    vyperWriteRaw? boundedStorage.locate? _ evm {base := name, steps := []}
      (.elem (.int (.uint ⟨256, by decide⟩))) (.int (Int.ofNat value.toNat))) = _
  simp only [vyperCheckRef?, vyperCheckSteps?, vyperWriteRaw?, vyperLeafLoc?, hloc,
    EvalResult.bind, EvalResult.ofOption, pure, bind, storageLocStore_uint256]

theorem vaultSlotWord_canonical {σ : AccountMap} {I : ExecutionEnv}
    (hwf : storageWF σ I) (slot : Nat) (hslot : slot < 5) :
    (codeOwnerStorageWord I σ (UInt256.ofNat slot)).toNat < 2 ^ 160 := by
  have h := hwf slot hslot
  unfold codeOwnerStorageWord
  cases hacc : σ.get? I.codeOwner with
  | none => change 0 < 2 ^ 160; decide +kernel
  | some acc =>
    rw [hacc] at h
    exact h

theorem vaultAddressReturnEncoding (w : UInt256) (hcanon : w.toNat < 2 ^ 160) :
    encodeReturnValue? (.elem .address) (.address (AccountAddress.ofNat w.toNat)) =
      some w.toByteArray := by
  have hword : EVM.Word.ofNat (AccountAddress.ofNat w.toNat).toNat = w :=
    by simpa only [keyValueToWord_address] using keyValueToWord_address_of_canonical w hcanon
  rw [Reasoning.VyperDispatch.addressReturnEncoding, hword]

theorem vaultWordReturn_read (w : UInt256) (mem : ByteArray) :
    (w.toByteArray.write 0 mem 64 32).readWithPadding 64 32 = w.toByteArray :=
  toByteArray_write_read_back_of_gap w mem 64
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 64 (by norm_num)))

theorem vaultControllerEval (evm : EVM.State) (locals : Store)
    (hlocals : locals.get? "_controller" = none) :
    evalExpr? config {contract := contract, locals := locals} evm
      (.cast (.storage {base := "_controller", steps := []}) (.elem .address)) =
      .ok (.address (AccountAddress.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat)) := by
  have h := vaultEvalScalar evm locals "_controller" (.int (.uint ⟨256, by decide⟩))
    ⟨3⟩ hlocals rfl rfl
  simp only [wordToElem, normalizeInt_uint256_word] at h
  rw [evalExpr?]
  simp only [h, EvalResult.bind, bind, castValue?, EvalResult.ofOption]
  have hn : ¬ (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩).toNat < 0) :=
    Int.not_lt.mpr (Int.natCast_nonneg _)
  rw [if_neg hn]
  rfl

end Benchmarks.CurveVault
