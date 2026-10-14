import Benchmarks.Safe.ViaIR.SetupEventTrace
import Benchmarks.Safe.ViaIR.SetupDataAllocate
import Benchmarks.Safe.ViaIR.SetupSource

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.ViaIR.safeSetupEventTrace, ``Benchmarks.Safe.ViaIR.safeSetupEventTraceRevert,
      ``Benchmarks.Safe.ViaIR.safeSetupEventStatic, ``Benchmarks.Safe.ViaIR.safeSetupOwnersAllocate,
      ``Benchmarks.Safe.ViaIR.safeSetupModulesAllocate, ``Benchmarks.Safe.ViaIR.safeSetupPrefix,
      ``Benchmarks.Safe.ViaIR.safeSetupStatic, ``Benchmarks.Safe.ViaIR.safeInternalSetupFallback] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
