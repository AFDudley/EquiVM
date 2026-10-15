import Benchmarks.Safe.ViaIR.ExecTransactionPrepare

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.ViaIR.safeExecTransactionPrepare,
      ``Benchmarks.Safe.ViaIR.safeExecTransactionNoncePrefix,
      ``Benchmarks.Safe.ViaIR.safeExecTransactionNonceOverflow,
      ``Benchmarks.Safe.ViaIR.safeExecTransactionNonceStatic,
      ``Benchmarks.Safe.ViaIR.safeExecHashTrace, ``Benchmarks.Safe.ViaIR.transactionHashMemory_preserves] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
