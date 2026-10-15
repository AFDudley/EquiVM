import Benchmarks.Safe.V2_0e91d99.SetupEventTrace
import Benchmarks.Safe.V2_0e91d99.SetupDataAllocate
import Benchmarks.Safe.V2_0e91d99.SetupSource

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V2_0e91d99.safeSetupEventTrace, ``Benchmarks.Safe.V2_0e91d99.safeSetupEventTraceRevert,
      ``Benchmarks.Safe.V2_0e91d99.safeSetupEventStatic, ``Benchmarks.Safe.V2_0e91d99.safeSetupOwnersAllocate,
      ``Benchmarks.Safe.V2_0e91d99.safeSetupModulesAllocate, ``Benchmarks.Safe.V2_0e91d99.safeSetupPrefix,
      ``Benchmarks.Safe.V2_0e91d99.safeSetupStatic, ``Benchmarks.Safe.V2_0e91d99.safeInternalSetupFallback] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
