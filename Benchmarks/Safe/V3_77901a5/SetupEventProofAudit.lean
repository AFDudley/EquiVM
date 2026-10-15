import Benchmarks.Safe.V3_77901a5.SetupEventTrace
import Benchmarks.Safe.V3_77901a5.SetupDataAllocate
import Benchmarks.Safe.V3_77901a5.SetupSource

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V3_77901a5.safeSetupEventTrace, ``Benchmarks.Safe.V3_77901a5.safeSetupEventTraceRevert,
      ``Benchmarks.Safe.V3_77901a5.safeSetupEventStatic, ``Benchmarks.Safe.V3_77901a5.safeSetupOwnersAllocate,
      ``Benchmarks.Safe.V3_77901a5.safeSetupModulesAllocate, ``Benchmarks.Safe.V3_77901a5.safeSetupPrefix,
      ``Benchmarks.Safe.V3_77901a5.safeSetupStatic, ``Benchmarks.Safe.V3_77901a5.safeInternalSetupFallback] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
