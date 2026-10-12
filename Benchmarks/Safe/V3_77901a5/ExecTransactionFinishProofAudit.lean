import Benchmarks.Safe.V3_77901a5.ExecTransactionFinish
import Benchmarks.Safe.V3_77901a5.ExecTransactionPaymentTrace
import Benchmarks.Safe.V3_77901a5.ExecTransactionSuccessCheck
import Benchmarks.Safe.V3_77901a5.ExecTransactionGasCheck

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V3_77901a5.safeExecTransactionFinish,
      ``Benchmarks.Safe.V3_77901a5.safeExecTransactionPayment, ``Benchmarks.Safe.V3_77901a5.safeExecSuccessCheck,
      ``Benchmarks.Safe.V3_77901a5.safeExecGasUsed, ``Benchmarks.Safe.V3_77901a5.safeExecTransactionExecute,
      ``Benchmarks.Safe.V3_77901a5.safeExecGasCheck, ``Benchmarks.Safe.V3_77901a5.safeExecAfterGuardTrace,
      ``Benchmarks.Safe.V3_77901a5.checkedSubSourceUnderflow] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
