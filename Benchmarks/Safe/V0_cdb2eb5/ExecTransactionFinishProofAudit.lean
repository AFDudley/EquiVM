import Benchmarks.Safe.V0_cdb2eb5.ExecTransactionFinish
import Benchmarks.Safe.V0_cdb2eb5.ExecTransactionPaymentTrace
import Benchmarks.Safe.V0_cdb2eb5.ExecTransactionSuccessCheck
import Benchmarks.Safe.V0_cdb2eb5.ExecTransactionGasCheck

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V0_cdb2eb5.safeExecTransactionFinish,
      ``Benchmarks.Safe.V0_cdb2eb5.safeExecTransactionPayment, ``Benchmarks.Safe.V0_cdb2eb5.safeExecSuccessCheck,
      ``Benchmarks.Safe.V0_cdb2eb5.safeExecGasUsed, ``Benchmarks.Safe.V0_cdb2eb5.safeExecTransactionExecute,
      ``Benchmarks.Safe.V0_cdb2eb5.safeExecGasCheck, ``Benchmarks.Safe.V0_cdb2eb5.safeExecAfterGuardTrace,
      ``Benchmarks.Safe.V0_cdb2eb5.checkedSubSourceUnderflow] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
