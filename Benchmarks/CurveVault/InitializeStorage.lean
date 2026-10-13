import Benchmarks.CurveVault.Storage
import Benchmarks.CurveVault.AddressWord
import Reasoning.VyperBounded

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperBounded
namespace Benchmarks.CurveVault

theorem vaultAssignScalarAddress (evm : State) (locals : Store) (name : Ident)
    (slot : UInt256) (value : AccountAddress) (hbase : locals.get? name = none)
    (hty : storageTypeAt? contract.storage {base := name, steps := []} = some (.elem .address))
    (hloc : boundedStorage.locate? {base := name, steps := []} = some (.leaf (vyperWordLoc slot .address))) :
    assignStorageRef? config {contract := contract, locals := locals} evm .storage
      {base := name, steps := []} (.address value) =
      .ok ({contract := contract, locals := locals},
        Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot (UInt256.ofNat value.val)) := by
  apply assignStorageRef_storage_of_write (er := {base := name, steps := []}) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]) hty
  change (do
    let _ ← vyperCheckRef? boundedStorage.locate? _ evm {base := name, steps := []}
    vyperWriteRaw? boundedStorage.locate? _ evm {base := name, steps := []} (.elem .address) (.address value)) = _
  simp only [vyperCheckRef?, vyperCheckSteps?, vyperWriteRaw?, vyperLeafLoc?, hloc,
    EvalResult.bind, EvalResult.ofOption, pure, bind, storageLocStore_vyperWord_address]

theorem vaultAssignController (evm : State) (locals : Store) (value : UInt256)
    (hbase : locals.get? "_controller" = none) (hcanon : value.toNat < EVM.addressModulus) :
    assignStorageRef? config {contract := contract, locals := locals} evm .storage
      {base := "_controller", steps := []} (.int (Int.ofNat value.toNat)) =
      .ok ({contract := contract, locals := locals},
        Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩ value) := by
  apply assignStorageRef_storage_of_write (er := {base := "_controller", steps := []}) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]) rfl
  have hnonneg : ¬ (Int.ofNat value.toNat < 0) := Int.not_lt.mpr (Int.natCast_nonneg _)
  have hsmall : ¬ (Int.ofNat value.toNat ≥ 2 ^ 160) := by
    change value.toNat < 2 ^ 160 at hcanon
    change ¬ (value.toNat : Int) ≥ (2 : Int) ^ 160
    exact_mod_cast Nat.not_le.mpr hcanon
  have hbackend : config.storageBackend.write {base := "_controller", steps := []}
      (.elem (.int (.uint ⟨256, by decide⟩))) (.int (Int.ofNat value.toNat)) evm =
      boundedStorage.write {base := "_controller", steps := []}
        (.elem (.int (.uint ⟨256, by decide⟩))) (.int (Int.ofNat value.toNat)) evm := by
    simp only [config, storageBackend, beq_self_eq_true, List.isEmpty_nil, hnonneg, hsmall,
      decide_false, Bool.false_or, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  rw [hbackend]
  have hloc : boundedStorage.locate? {base := "_controller", steps := []} = some (.leaf (uint256Loc ⟨3⟩)) := rfl
  change (do
    let _ ← vyperCheckRef? boundedStorage.locate? _ evm {base := "_controller", steps := []}
    vyperWriteRaw? boundedStorage.locate? _ evm {base := "_controller", steps := []}
      (.elem (.int (.uint ⟨256, by decide⟩))) (.int (Int.ofNat value.toNat))) = _
  simp only [vyperCheckRef?, vyperCheckSteps?, vyperWriteRaw?, vyperLeafLoc?, hloc,
    EvalResult.bind, EvalResult.ofOption, pure, bind, storageLocStore_uint256]

end Benchmarks.CurveVault
