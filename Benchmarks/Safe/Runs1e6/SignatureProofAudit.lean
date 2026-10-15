import Benchmarks.Safe.Runs1e6.CheckNSignatures
import Benchmarks.Safe.Runs1e6.CheckSignatures
import Benchmarks.Safe.Runs1e6.CheckNSignaturesAddress
import Benchmarks.Safe.Runs1e6.CheckSignaturesAddress

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.Runs1e6.safeChecknsignaturesBodyCore,
      ``Benchmarks.Safe.Runs1e6.safeChecksignaturesBodyCore,
      ``Benchmarks.Safe.Runs1e6.safeChecknsignaturesAddressBytes32BytesUint256BodyCore,
      ``Benchmarks.Safe.Runs1e6.safeChecksignaturesAddressBytes32BytesBodyCore] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
