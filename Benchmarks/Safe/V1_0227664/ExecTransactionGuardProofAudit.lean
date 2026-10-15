import Benchmarks.Safe.V1_0227664.ExecTransactionGuardTrace

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V1_0227664.safeExecTransactionGuard,
      ``Benchmarks.Safe.V1_0227664.safeExecGuardCallTrace, ``Benchmarks.Safe.V1_0227664.safeExecGuardEncode,
      ``Benchmarks.Safe.V1_0227664.safeExecGuardCallEncoding, ``Benchmarks.Safe.V1_0227664.execGuardArgsMemory_read,
      ``Benchmarks.Safe.V1_0227664.optionalCheckedCallSuccess,
      ``Benchmarks.Safe.V1_0227664.calldataBytesEncodedInto_read] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
