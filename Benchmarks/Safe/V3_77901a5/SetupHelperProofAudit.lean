import Benchmarks.Safe.V3_77901a5.SetupOwnersTrace
import Benchmarks.Safe.V3_77901a5.SetupModulesTrace

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V3_77901a5.safeSetupOwnersTrace, ``Benchmarks.Safe.V3_77901a5.safeSetupModulesTrace,
      ``Benchmarks.Safe.V3_77901a5.safeInternalSetupOwners, ``Benchmarks.Safe.V3_77901a5.safeInternalSetupModules] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
