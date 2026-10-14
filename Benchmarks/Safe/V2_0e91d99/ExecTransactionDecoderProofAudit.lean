import Benchmarks.Safe.V2_0e91d99.ExecTransactionDecoderEvidence

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V2_0e91d99.safeDecodeExecTransactionValid,
      ``Benchmarks.Safe.V2_0e91d99.safeDecodeExecTransactionEvidence,
      ``Benchmarks.Safe.V2_0e91d99.decodeExecTransactionValid,
      ``Benchmarks.Safe.V2_0e91d99.decodeExecTransactionEvidence] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
