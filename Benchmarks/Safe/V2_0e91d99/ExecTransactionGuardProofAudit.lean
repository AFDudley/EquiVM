import Benchmarks.Safe.V2_0e91d99.ExecTransactionGuardTrace

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V2_0e91d99.safeExecTransactionGuard,
      ``Benchmarks.Safe.V2_0e91d99.safeExecGuardCallTrace, ``Benchmarks.Safe.V2_0e91d99.safeExecGuardEncode,
      ``Benchmarks.Safe.V2_0e91d99.safeExecGuardCallEncoding, ``Benchmarks.Safe.V2_0e91d99.execGuardArgsMemory_read,
      ``Benchmarks.Safe.V2_0e91d99.optionalCheckedCallSuccess,
      ``Benchmarks.Safe.V2_0e91d99.calldataBytesEncodedInto_read] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
