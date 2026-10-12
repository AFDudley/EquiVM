import Benchmarks.Safe.V2_0e91d99.CheckNSignatures
import Benchmarks.Safe.V2_0e91d99.CheckSignatures
import Benchmarks.Safe.V2_0e91d99.CheckNSignaturesAddress
import Benchmarks.Safe.V2_0e91d99.CheckSignaturesAddress

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V2_0e91d99.safeChecknsignaturesBodyCore,
      ``Benchmarks.Safe.V2_0e91d99.safeChecksignaturesBodyCore,
      ``Benchmarks.Safe.V2_0e91d99.safeChecknsignaturesAddressBytes32BytesUint256BodyCore,
      ``Benchmarks.Safe.V2_0e91d99.safeChecksignaturesAddressBytes32BytesBodyCore] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
