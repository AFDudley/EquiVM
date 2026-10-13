import Benchmarks.Safe.ViaIR.SetupDecoder

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.ViaIR.safeDecodeSetupValid, ``Benchmarks.Safe.ViaIR.safeDecodeSetupEvidence,
      ``Benchmarks.Safe.ViaIR.decodeSetupBounded, ``Benchmarks.Safe.ViaIR.decodeSetupEvidence] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
