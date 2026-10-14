import Benchmarks.Safe.V1_0227664.ExecTransactionDecoderEvidence

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V1_0227664.safeDecodeExecTransactionValid,
      ``Benchmarks.Safe.V1_0227664.safeDecodeExecTransactionEvidence,
      ``Benchmarks.Safe.V1_0227664.decodeExecTransactionValid,
      ``Benchmarks.Safe.V1_0227664.decodeExecTransactionEvidence] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
