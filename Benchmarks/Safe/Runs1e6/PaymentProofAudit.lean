import Benchmarks.Safe.Runs1e6.PaymentTrace

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.Runs1e6.safeTokenTransferTrace, ``Benchmarks.Safe.Runs1e6.safePaymentTrace,
      ``Benchmarks.Safe.Runs1e6.safeInternalPayment] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
