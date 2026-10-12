import Benchmarks.Safe.Main.ExecTransactionPrepare

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.Main.safeExecTransactionPrepare,
      ``Benchmarks.Safe.Main.safeExecTransactionNoncePrefix,
      ``Benchmarks.Safe.Main.safeExecTransactionNonceOverflow,
      ``Benchmarks.Safe.Main.safeExecTransactionNonceStatic,
      ``Benchmarks.Safe.Main.safeExecHashTrace, ``Benchmarks.Safe.Main.transactionHashMemory_preserves] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
