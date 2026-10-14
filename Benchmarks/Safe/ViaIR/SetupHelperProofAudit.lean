import Benchmarks.Safe.ViaIR.SetupOwnersTrace
import Benchmarks.Safe.ViaIR.SetupModulesTrace

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.ViaIR.safeSetupOwnersTrace, ``Benchmarks.Safe.ViaIR.safeSetupModulesTrace,
      ``Benchmarks.Safe.ViaIR.safeInternalSetupOwners, ``Benchmarks.Safe.ViaIR.safeInternalSetupModules] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
