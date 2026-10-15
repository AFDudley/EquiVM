import Benchmarks.Safe.ViaIR.ExecTransactionGuardTrace

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.ViaIR.safeExecTransactionGuard,
      ``Benchmarks.Safe.ViaIR.safeExecGuardCallTrace, ``Benchmarks.Safe.ViaIR.safeExecGuardEncode,
      ``Benchmarks.Safe.ViaIR.safeExecGuardCallEncoding, ``Benchmarks.Safe.ViaIR.execGuardArgsMemory_read,
      ``Benchmarks.Safe.ViaIR.optionalCheckedCallSuccess,
      ``Benchmarks.Safe.ViaIR.calldataBytesEncodedInto_read] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
