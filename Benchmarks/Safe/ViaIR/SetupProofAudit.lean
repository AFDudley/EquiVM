import Benchmarks.Safe.ViaIR.Setup

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.ViaIR.safeSetupBodyCore, ``Benchmarks.Safe.ViaIR.safeSetupBodyTrace,
      ``Benchmarks.Safe.ViaIR.safeSetupFallbackTrace, ``Benchmarks.Safe.ViaIR.safeSetupModulesCallTrace,
      ``Benchmarks.Safe.ViaIR.safeSetupPaymentTrace] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
