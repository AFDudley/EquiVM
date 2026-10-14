import Benchmarks.Safe.V0_cdb2eb5.Setup

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V0_cdb2eb5.safeSetupBodyCore, ``Benchmarks.Safe.V0_cdb2eb5.safeSetupBodyTrace,
      ``Benchmarks.Safe.V0_cdb2eb5.safeSetupFallbackTrace, ``Benchmarks.Safe.V0_cdb2eb5.safeSetupModulesCallTrace,
      ``Benchmarks.Safe.V0_cdb2eb5.safeSetupPaymentTrace] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
