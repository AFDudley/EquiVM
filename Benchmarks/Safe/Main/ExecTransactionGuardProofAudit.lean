import Benchmarks.Safe.Main.ExecTransactionGuardTrace

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.Main.safeExecTransactionGuard,
      ``Benchmarks.Safe.Main.safeExecGuardCallTrace, ``Benchmarks.Safe.Main.safeExecGuardEncode,
      ``Benchmarks.Safe.Main.safeExecGuardCallEncoding, ``Benchmarks.Safe.Main.execGuardArgsMemory_read,
      ``Benchmarks.Safe.Main.optionalCheckedCallSuccess,
      ``Benchmarks.Safe.Main.calldataBytesEncodedInto_read] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
