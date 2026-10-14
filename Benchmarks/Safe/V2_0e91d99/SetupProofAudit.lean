import Benchmarks.Safe.V2_0e91d99.Setup

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V2_0e91d99.safeSetupBodyCore, ``Benchmarks.Safe.V2_0e91d99.safeSetupBodyTrace,
      ``Benchmarks.Safe.V2_0e91d99.safeSetupFallbackTrace, ``Benchmarks.Safe.V2_0e91d99.safeSetupModulesCallTrace,
      ``Benchmarks.Safe.V2_0e91d99.safeSetupPaymentTrace] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
