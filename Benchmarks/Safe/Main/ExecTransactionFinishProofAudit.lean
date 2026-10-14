import Benchmarks.Safe.Main.ExecTransactionFinish
import Benchmarks.Safe.Main.ExecTransactionPaymentTrace
import Benchmarks.Safe.Main.ExecTransactionSuccessCheck
import Benchmarks.Safe.Main.ExecTransactionGasCheck

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.Main.safeExecTransactionFinish,
      ``Benchmarks.Safe.Main.safeExecTransactionPayment, ``Benchmarks.Safe.Main.safeExecSuccessCheck,
      ``Benchmarks.Safe.Main.safeExecGasUsed, ``Benchmarks.Safe.Main.safeExecTransactionExecute,
      ``Benchmarks.Safe.Main.safeExecGasCheck, ``Benchmarks.Safe.Main.safeExecAfterGuardTrace,
      ``Benchmarks.Safe.Main.checkedSubSourceUnderflow] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
