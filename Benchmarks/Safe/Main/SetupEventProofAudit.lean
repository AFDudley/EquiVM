import Benchmarks.Safe.Main.SetupEventTrace
import Benchmarks.Safe.Main.SetupDataAllocate
import Benchmarks.Safe.Main.SetupSource

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.Main.safeSetupEventTrace, ``Benchmarks.Safe.Main.safeSetupEventTraceRevert,
      ``Benchmarks.Safe.Main.safeSetupEventStatic, ``Benchmarks.Safe.Main.safeSetupOwnersAllocate,
      ``Benchmarks.Safe.Main.safeSetupModulesAllocate, ``Benchmarks.Safe.Main.safeSetupPrefix,
      ``Benchmarks.Safe.Main.safeSetupStatic, ``Benchmarks.Safe.Main.safeInternalSetupFallback] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
