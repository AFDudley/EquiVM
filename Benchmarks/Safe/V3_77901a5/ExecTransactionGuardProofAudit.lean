import Benchmarks.Safe.V3_77901a5.ExecTransactionGuardTrace

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V3_77901a5.safeExecTransactionGuard,
      ``Benchmarks.Safe.V3_77901a5.safeExecGuardCallTrace, ``Benchmarks.Safe.V3_77901a5.safeExecGuardEncode,
      ``Benchmarks.Safe.V3_77901a5.safeExecGuardCallEncoding, ``Benchmarks.Safe.V3_77901a5.execGuardArgsMemory_read,
      ``Benchmarks.Safe.V3_77901a5.optionalCheckedCallSuccess,
      ``Benchmarks.Safe.V3_77901a5.calldataBytesEncodedInto_read] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
