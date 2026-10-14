import Benchmarks.Safe.V2_0e91d99.ExecTransactionPrepare

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V2_0e91d99.safeExecTransactionPrepare,
      ``Benchmarks.Safe.V2_0e91d99.safeExecTransactionNoncePrefix,
      ``Benchmarks.Safe.V2_0e91d99.safeExecTransactionNonceOverflow,
      ``Benchmarks.Safe.V2_0e91d99.safeExecTransactionNonceStatic,
      ``Benchmarks.Safe.V2_0e91d99.safeExecHashTrace, ``Benchmarks.Safe.V2_0e91d99.transactionHashMemory_preserves] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
