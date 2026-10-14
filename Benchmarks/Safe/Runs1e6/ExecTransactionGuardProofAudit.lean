import Benchmarks.Safe.Runs1e6.ExecTransactionGuardTrace

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.Runs1e6.safeExecTransactionGuard,
      ``Benchmarks.Safe.Runs1e6.safeExecGuardCallTrace, ``Benchmarks.Safe.Runs1e6.safeExecGuardEncode,
      ``Benchmarks.Safe.Runs1e6.safeExecGuardCallEncoding, ``Benchmarks.Safe.Runs1e6.execGuardArgsMemory_read,
      ``Benchmarks.Safe.Runs1e6.optionalCheckedCallSuccess,
      ``Benchmarks.Safe.Runs1e6.calldataBytesEncodedInto_read] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
