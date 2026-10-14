import Benchmarks.Safe.ViaIR.ExecTransactionFinish
import Benchmarks.Safe.ViaIR.ExecTransactionPaymentTrace
import Benchmarks.Safe.ViaIR.ExecTransactionSuccessCheck
import Benchmarks.Safe.ViaIR.ExecTransactionGasCheck

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.ViaIR.safeExecTransactionFinish,
      ``Benchmarks.Safe.ViaIR.safeExecTransactionPayment, ``Benchmarks.Safe.ViaIR.safeExecSuccessCheck,
      ``Benchmarks.Safe.ViaIR.safeExecGasUsed, ``Benchmarks.Safe.ViaIR.safeExecTransactionExecute,
      ``Benchmarks.Safe.ViaIR.safeExecGasCheck, ``Benchmarks.Safe.ViaIR.safeExecAfterGuardTrace,
      ``Benchmarks.Safe.ViaIR.checkedSubSourceUnderflow] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
