import Benchmarks.Safe.Runs1e6.ExecTransactionFinish
import Benchmarks.Safe.Runs1e6.ExecTransactionPaymentTrace
import Benchmarks.Safe.Runs1e6.ExecTransactionSuccessCheck
import Benchmarks.Safe.Runs1e6.ExecTransactionGasCheck

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.Runs1e6.safeExecTransactionFinish,
      ``Benchmarks.Safe.Runs1e6.safeExecTransactionPayment, ``Benchmarks.Safe.Runs1e6.safeExecSuccessCheck,
      ``Benchmarks.Safe.Runs1e6.safeExecGasUsed, ``Benchmarks.Safe.Runs1e6.safeExecTransactionExecute,
      ``Benchmarks.Safe.Runs1e6.safeExecGasCheck, ``Benchmarks.Safe.Runs1e6.safeExecAfterGuardTrace,
      ``Benchmarks.Safe.Runs1e6.checkedSubSourceUnderflow] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
