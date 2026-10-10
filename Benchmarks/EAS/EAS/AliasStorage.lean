import Benchmarks.EAS.EAS.Storage
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- GENERALIZES Reasoning.SolmBody.evalExpr_storage_scalar_value to resolved local storage aliases.
theorem evalExpr_storage_resolved_value {cfg : Config} {layout : StorageLayout}
    {solm : Frame} {evm : EVM.State} {slot : StorageRef}
    {er : EvaledStorageRef} {t : ABI.ElemType} {loc : StorageLoc} {value : Value}
    (hresolve : resolveStorageRef? cfg solm evm slot = .ok (er, .elem t))
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hloc : layout er = some (.leaf loc))
    (hload : storageLocLoad evm loc = value) :
    evalExpr? cfg solm evm (.storage slot) = .ok value := by
  rw [evalExpr?]
  simp only [hresolve, bind, EvalResult.bind, readStorage?_elem hbackend hloc, hload]

-- GENERALIZES Reasoning.SolmBody.assignStorageRef_storage_scalar_value to local storage aliases.
theorem assignStorageRef_resolved_value {cfg : Config} {layout : StorageLayout}
    {solm : Frame} {evm evm' : EVM.State} {slot : StorageRef}
    {er : EvaledStorageRef} {ty : StorageType} {loc : StorageLoc} {value : Value}
    (hresolve : resolveStorageRef? cfg solm evm slot = .ok (er, ty))
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hloc : layout er = some (.leaf loc))
    (hleaf : (∃ t, ty = .elem t) ∨ (∃ name, ty = .contract name))
    (hstore : storageLocStore evm loc value = some evm') :
    assignStorageRef? cfg solm evm .storage slot value = .ok (solm, evm') := by
  rcases hleaf with ⟨t, rfl⟩ | ⟨name, rfl⟩
  all_goals simp [assignStorageRef?, hresolve, hbackend, solidityStorageBackend,
    solidityWriteStorage?, solidityLeafLoc?_of_leaf hloc, hstore,
    EvalResult.ofOption, EvalResult.bind, bind, pure]

end Benchmarks.EAS.EAS
