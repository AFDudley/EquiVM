import Benchmarks.Safe.V2_0e91d99.SetupDecoder

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V2_0e91d99.safeDecodeSetupValid, ``Benchmarks.Safe.V2_0e91d99.safeDecodeSetupEvidence,
      ``Benchmarks.Safe.V2_0e91d99.decodeSetupBounded, ``Benchmarks.Safe.V2_0e91d99.decodeSetupEvidence] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
