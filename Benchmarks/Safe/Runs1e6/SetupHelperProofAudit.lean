import Benchmarks.Safe.Runs1e6.SetupOwnersTrace
import Benchmarks.Safe.Runs1e6.SetupModulesTrace

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.Runs1e6.safeSetupOwnersTrace, ``Benchmarks.Safe.Runs1e6.safeSetupModulesTrace,
      ``Benchmarks.Safe.Runs1e6.safeInternalSetupOwners, ``Benchmarks.Safe.Runs1e6.safeInternalSetupModules] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
