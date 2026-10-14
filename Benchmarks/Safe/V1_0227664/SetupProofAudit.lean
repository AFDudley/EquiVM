import Benchmarks.Safe.V1_0227664.Setup

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V1_0227664.safeSetupBodyCore, ``Benchmarks.Safe.V1_0227664.safeSetupBodyTrace,
      ``Benchmarks.Safe.V1_0227664.safeSetupFallbackTrace, ``Benchmarks.Safe.V1_0227664.safeSetupModulesCallTrace,
      ``Benchmarks.Safe.V1_0227664.safeSetupPaymentTrace] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
