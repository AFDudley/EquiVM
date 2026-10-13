import Benchmarks.CurveVault.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultBalanceEval (evm : EVM.State) (locals : Store) (argName : Ident) (a : AccountAddress)
    (hbase : locals.get? "balanceOf" = none)
    (harg : locals.get? argName = some (.address a)) :
    evalExpr? config {contract := contract, locals := locals} evm
      (.storage {base := "balanceOf", steps := [.mindex (.var argName)]}) =
      .ok (.int (Int.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (vyperMappingSlot ⟨13⟩ (.address a))).toNat)) := by
  have harg' : locals[argName]? = some (.address a) := harg
  apply evalExpr_storage_scalar_of_read
    (er := {base := "balanceOf", steps := [.mindex (.address a)]}) hbase
    (by simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, harg',
      valueToKey?, EvalResult.bind, EvalResult.ofOption, pure, bind]) (by rfl)
  have h := vaultReadMapping evm "balanceOf" [.address a] (.int (.uint ⟨256, by decide⟩))
    (vyperMappingSlot ⟨13⟩ (.address a)) rfl
  simpa only [wordToElem, normalizeInt_uint256_word] using h

theorem vaultBalanceAssign (evm : State) (locals : Store) (argName : Ident)
    (a : AccountAddress) (value : UInt256) (hbase : locals.get? "balanceOf" = none)
    (harg : locals.get? argName = some (.address a)) :
    assignStorageRef? config {contract := contract, locals := locals} evm .storage
      {base := "balanceOf", steps := [.mindex (.var argName)]} (.int (Int.ofNat value.toNat)) =
      .ok ({contract := contract, locals := locals},
        Solm.EVM.storageStore evm evm.executionEnv.codeOwner (vyperMappingSlot ⟨13⟩ (.address a)) value) := by
  apply assignStorageRef_storage_of_write
    (er := {base := "balanceOf", steps := [.mindex (.address a)]}) hbase
    (by simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, harg,
      valueToKey?, EvalResult.bind, EvalResult.ofOption, pure, bind]) rfl
  change (do
    let _ ← vyperCheckRef? boundedStorage.locate? _ evm {base := "balanceOf", steps := [.mindex (.address a)]}
    vyperWriteRaw? boundedStorage.locate? _ evm {base := "balanceOf", steps := [.mindex (.address a)]}
      (.elem (.int (.uint ⟨256, by decide⟩))) (.int (Int.ofNat value.toNat))) = _
  have hloc : boundedStorage.locate? {base := "balanceOf", steps := [.mindex (.address a)]} =
      some (.leaf (uint256Loc (vyperMappingSlot ⟨13⟩ (.address a)))) := rfl
  simp only [vyperCheckRef?, vyperCheckSteps?, vyperWriteRaw?, vyperLeafLoc?, hloc,
    EvalResult.bind, EvalResult.ofOption, pure, bind, storageLocStore_uint256]

end Benchmarks.CurveVault
