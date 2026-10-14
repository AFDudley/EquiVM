import Benchmarks.Safe.V0_cdb2eb5.SetupOwnersTrace
import Benchmarks.Safe.V0_cdb2eb5.SetupModulesTrace

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V0_cdb2eb5.safeSetupOwnersTrace, ``Benchmarks.Safe.V0_cdb2eb5.safeSetupModulesTrace,
      ``Benchmarks.Safe.V0_cdb2eb5.safeInternalSetupOwners, ``Benchmarks.Safe.V0_cdb2eb5.safeInternalSetupModules] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
