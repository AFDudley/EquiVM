import Benchmarks.Safe.V2_0e91d99.PaymentTrace

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V2_0e91d99.safeTokenTransferTrace, ``Benchmarks.Safe.V2_0e91d99.safePaymentTrace,
      ``Benchmarks.Safe.V2_0e91d99.safeInternalPayment] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
