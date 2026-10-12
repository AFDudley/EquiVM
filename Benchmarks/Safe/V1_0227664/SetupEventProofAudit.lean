import Benchmarks.Safe.V1_0227664.SetupEventTrace
import Benchmarks.Safe.V1_0227664.SetupDataAllocate
import Benchmarks.Safe.V1_0227664.SetupSource

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V1_0227664.safeSetupEventTrace, ``Benchmarks.Safe.V1_0227664.safeSetupEventTraceRevert,
      ``Benchmarks.Safe.V1_0227664.safeSetupEventStatic, ``Benchmarks.Safe.V1_0227664.safeSetupOwnersAllocate,
      ``Benchmarks.Safe.V1_0227664.safeSetupModulesAllocate, ``Benchmarks.Safe.V1_0227664.safeSetupPrefix,
      ``Benchmarks.Safe.V1_0227664.safeSetupStatic, ``Benchmarks.Safe.V1_0227664.safeInternalSetupFallback] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
