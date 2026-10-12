import Benchmarks.Safe.V2_0e91d99.SetupOwnersTrace
import Benchmarks.Safe.V2_0e91d99.SetupModulesTrace

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V2_0e91d99.safeSetupOwnersTrace, ``Benchmarks.Safe.V2_0e91d99.safeSetupModulesTrace,
      ``Benchmarks.Safe.V2_0e91d99.safeInternalSetupOwners, ``Benchmarks.Safe.V2_0e91d99.safeInternalSetupModules] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
