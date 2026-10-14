import Benchmarks.Safe.V2_0e91d99.ExecTransactionFinish
import Benchmarks.Safe.V2_0e91d99.ExecTransactionPaymentTrace
import Benchmarks.Safe.V2_0e91d99.ExecTransactionSuccessCheck
import Benchmarks.Safe.V2_0e91d99.ExecTransactionGasCheck

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V2_0e91d99.safeExecTransactionFinish,
      ``Benchmarks.Safe.V2_0e91d99.safeExecTransactionPayment, ``Benchmarks.Safe.V2_0e91d99.safeExecSuccessCheck,
      ``Benchmarks.Safe.V2_0e91d99.safeExecGasUsed, ``Benchmarks.Safe.V2_0e91d99.safeExecTransactionExecute,
      ``Benchmarks.Safe.V2_0e91d99.safeExecGasCheck, ``Benchmarks.Safe.V2_0e91d99.safeExecAfterGuardTrace,
      ``Benchmarks.Safe.V2_0e91d99.checkedSubSourceUnderflow] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
