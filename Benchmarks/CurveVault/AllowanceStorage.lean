import Benchmarks.CurveVault.Storage

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultAllowanceSlot (owner spender : AccountAddress) : UInt256 :=
  vyperMappingSlot (vyperMappingSlot ⟨12⟩ (.address owner)) (.address spender)

theorem vaultAllowanceEvalAt (evm : State) (locals : Store) (owner spender : Expr)
    (a b : AccountAddress) (hbase : locals.get? "allowance" = none)
    (ha : evalExpr? config {contract := contract, locals := locals} evm owner = .ok (.address a))
    (hb : evalExpr? config {contract := contract, locals := locals} evm spender = .ok (.address b)) :
    evalExpr? config {contract := contract, locals := locals} evm
      (.storage {base := "allowance", steps := [.mindex owner, .mindex spender]}) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner
        (vaultAllowanceSlot a b)).toNat)) := by
  apply evalExpr_storage_scalar_of_read
    (er := {base := "allowance", steps := [.mindex (.address a), .mindex (.address b)]}) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, ha, hb,
      valueToKey?, EvalResult.bind, EvalResult.ofOption, pure, bind]) rfl
  have h := vaultReadMapping evm "allowance" [.address a, .address b] (.int (.uint ⟨256, by decide⟩))
    (vaultAllowanceSlot a b) rfl
  simpa only [wordToElem, normalizeInt_uint256_word] using h

theorem vaultAllowanceAssign (evm : State) (locals : Store) (owner spender : Expr)
    (a b : AccountAddress) (value : UInt256) (hbase : locals.get? "allowance" = none)
    (ha : evalExpr? config {contract := contract, locals := locals} evm owner = .ok (.address a))
    (hb : evalExpr? config {contract := contract, locals := locals} evm spender = .ok (.address b)) :
    assignStorageRef? config {contract := contract, locals := locals} evm .storage
      {base := "allowance", steps := [.mindex owner, .mindex spender]} (.int (Int.ofNat value.toNat)) =
      .ok ({contract := contract, locals := locals},
        Stele.EVM.storageStore evm evm.executionEnv.codeOwner (vaultAllowanceSlot a b) value) := by
  apply assignStorageRef_storage_of_write
    (er := {base := "allowance", steps := [.mindex (.address a), .mindex (.address b)]})
    hbase
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, ha, hb,
      valueToKey?, EvalResult.bind, EvalResult.ofOption, pure, bind])
    rfl
  change (do
    let _ ← vyperCheckRef? boundedStorage.locate? _ evm
      {base := "allowance", steps := [.mindex (.address a), .mindex (.address b)]}
    vyperWriteRaw? boundedStorage.locate? _ evm
      {base := "allowance", steps := [.mindex (.address a), .mindex (.address b)]}
      (.elem (.int (.uint ⟨256, by decide⟩))) (.int (Int.ofNat value.toNat))) = _
  have hloc : boundedStorage.locate?
      {base := "allowance", steps := [.mindex (.address a), .mindex (.address b)]} =
      some (.leaf (uint256Loc (vaultAllowanceSlot a b))) := rfl
  simp only [vyperCheckRef?, vyperCheckSteps?, vyperWriteRaw?, vyperLeafLoc?, hloc,
    EvalResult.bind, EvalResult.ofOption, pure, bind, storageLocStore_uint256]

end Benchmarks.CurveVault
