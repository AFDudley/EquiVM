import Benchmarks.Safe.Runs1e6.Setup

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.Runs1e6.safeSetupBodyCore, ``Benchmarks.Safe.Runs1e6.safeSetupBodyTrace,
      ``Benchmarks.Safe.Runs1e6.safeSetupFallbackTrace, ``Benchmarks.Safe.Runs1e6.safeSetupModulesCallTrace,
      ``Benchmarks.Safe.Runs1e6.safeSetupPaymentTrace] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
