import Benchmarks.Safe.Runs1e6.SetupEventTrace
import Benchmarks.Safe.Runs1e6.SetupDataAllocate
import Benchmarks.Safe.Runs1e6.SetupSource

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.Runs1e6.safeSetupEventTrace, ``Benchmarks.Safe.Runs1e6.safeSetupEventTraceRevert,
      ``Benchmarks.Safe.Runs1e6.safeSetupEventStatic, ``Benchmarks.Safe.Runs1e6.safeSetupOwnersAllocate,
      ``Benchmarks.Safe.Runs1e6.safeSetupModulesAllocate, ``Benchmarks.Safe.Runs1e6.safeSetupPrefix,
      ``Benchmarks.Safe.Runs1e6.safeSetupStatic, ``Benchmarks.Safe.Runs1e6.safeInternalSetupFallback] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
