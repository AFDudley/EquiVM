import Benchmarks.Safe.V3_77901a5.ExecTransactionDecoderEvidence

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V3_77901a5.safeDecodeExecTransactionValid,
      ``Benchmarks.Safe.V3_77901a5.safeDecodeExecTransactionEvidence,
      ``Benchmarks.Safe.V3_77901a5.decodeExecTransactionValid,
      ``Benchmarks.Safe.V3_77901a5.decodeExecTransactionEvidence] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
