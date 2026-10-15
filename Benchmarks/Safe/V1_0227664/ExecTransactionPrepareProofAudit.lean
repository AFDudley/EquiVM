import Benchmarks.Safe.V1_0227664.ExecTransactionPrepare

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V1_0227664.safeExecTransactionPrepare,
      ``Benchmarks.Safe.V1_0227664.safeExecTransactionNoncePrefix,
      ``Benchmarks.Safe.V1_0227664.safeExecTransactionNonceOverflow,
      ``Benchmarks.Safe.V1_0227664.safeExecTransactionNonceStatic,
      ``Benchmarks.Safe.V1_0227664.safeExecHashTrace, ``Benchmarks.Safe.V1_0227664.transactionHashMemory_preserves] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
