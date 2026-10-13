import Benchmarks.EAS.EAS.Storage
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- GENERALIZES Reasoning.SteleBody.evalExpr_storage_scalar_value to resolved local storage aliases.
theorem evalExpr_storage_resolved_value {cfg : Config} {layout : StorageLayout}
    {stele : Frame} {evm : EVM.State} {slot : StorageRef}
    {er : EvaledStorageRef} {t : ABI.ElemType} {loc : StorageLoc} {value : Value}
    (hresolve : resolveStorageRef? cfg stele evm slot = .ok (er, .elem t))
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hloc : layout er = some (.leaf loc))
    (hload : storageLocLoad evm loc = value) :
    evalExpr? cfg stele evm (.storage slot) = .ok value := by
  rw [evalExpr?]
  simp only [hresolve, bind, EvalResult.bind, readStorage?_elem hbackend hloc, hload]

-- GENERALIZES Reasoning.SteleBody.assignStorageRef_storage_scalar_value to local storage aliases.
theorem assignStorageRef_resolved_value {cfg : Config} {layout : StorageLayout}
    {stele : Frame} {evm evm' : EVM.State} {slot : StorageRef}
    {er : EvaledStorageRef} {ty : StorageType} {loc : StorageLoc} {value : Value}
    (hresolve : resolveStorageRef? cfg stele evm slot = .ok (er, ty))
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hloc : layout er = some (.leaf loc))
    (hleaf : (∃ t, ty = .elem t) ∨ (∃ name, ty = .contract name))
    (hstore : storageLocStore evm loc value = some evm') :
    assignStorageRef? cfg stele evm .storage slot value = .ok (stele, evm') := by
  rcases hleaf with ⟨t, rfl⟩ | ⟨name, rfl⟩
  all_goals simp [assignStorageRef?, hresolve, hbackend, solidityStorageBackend,
    solidityWriteStorage?, solidityLeafLoc?_of_leaf hloc, hstore,
    EvalResult.ofOption, EvalResult.bind, bind, pure]

end Benchmarks.EAS.EAS
