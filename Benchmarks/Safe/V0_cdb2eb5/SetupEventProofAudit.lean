import Benchmarks.Safe.V0_cdb2eb5.SetupEventTrace
import Benchmarks.Safe.V0_cdb2eb5.SetupDataAllocate
import Benchmarks.Safe.V0_cdb2eb5.SetupSource

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V0_cdb2eb5.safeSetupEventTrace, ``Benchmarks.Safe.V0_cdb2eb5.safeSetupEventTraceRevert,
      ``Benchmarks.Safe.V0_cdb2eb5.safeSetupEventStatic, ``Benchmarks.Safe.V0_cdb2eb5.safeSetupOwnersAllocate,
      ``Benchmarks.Safe.V0_cdb2eb5.safeSetupModulesAllocate, ``Benchmarks.Safe.V0_cdb2eb5.safeSetupPrefix,
      ``Benchmarks.Safe.V0_cdb2eb5.safeSetupStatic, ``Benchmarks.Safe.V0_cdb2eb5.safeInternalSetupFallback] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
