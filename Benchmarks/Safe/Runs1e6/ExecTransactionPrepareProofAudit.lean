import Benchmarks.Safe.Runs1e6.ExecTransactionPrepare

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.Runs1e6.safeExecTransactionPrepare,
      ``Benchmarks.Safe.Runs1e6.safeExecTransactionNoncePrefix,
      ``Benchmarks.Safe.Runs1e6.safeExecTransactionNonceOverflow,
      ``Benchmarks.Safe.Runs1e6.safeExecTransactionNonceStatic,
      ``Benchmarks.Safe.Runs1e6.safeExecHashTrace, ``Benchmarks.Safe.Runs1e6.transactionHashMemory_preserves] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
