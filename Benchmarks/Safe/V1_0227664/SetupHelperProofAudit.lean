import Benchmarks.Safe.V1_0227664.SetupOwnersTrace
import Benchmarks.Safe.V1_0227664.SetupModulesTrace

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V1_0227664.safeSetupOwnersTrace, ``Benchmarks.Safe.V1_0227664.safeSetupModulesTrace,
      ``Benchmarks.Safe.V1_0227664.safeInternalSetupOwners, ``Benchmarks.Safe.V1_0227664.safeInternalSetupModules] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
