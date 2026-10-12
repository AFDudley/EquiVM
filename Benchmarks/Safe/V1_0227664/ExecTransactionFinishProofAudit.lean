import Benchmarks.Safe.V1_0227664.ExecTransactionFinish
import Benchmarks.Safe.V1_0227664.ExecTransactionPaymentTrace
import Benchmarks.Safe.V1_0227664.ExecTransactionSuccessCheck
import Benchmarks.Safe.V1_0227664.ExecTransactionGasCheck

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V1_0227664.safeExecTransactionFinish,
      ``Benchmarks.Safe.V1_0227664.safeExecTransactionPayment, ``Benchmarks.Safe.V1_0227664.safeExecSuccessCheck,
      ``Benchmarks.Safe.V1_0227664.safeExecGasUsed, ``Benchmarks.Safe.V1_0227664.safeExecTransactionExecute,
      ``Benchmarks.Safe.V1_0227664.safeExecGasCheck, ``Benchmarks.Safe.V1_0227664.safeExecAfterGuardTrace,
      ``Benchmarks.Safe.V1_0227664.checkedSubSourceUnderflow] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
