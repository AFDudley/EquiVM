import Benchmarks.Safe.V0_cdb2eb5.CheckNSignatures
import Benchmarks.Safe.V0_cdb2eb5.CheckSignatures
import Benchmarks.Safe.V0_cdb2eb5.CheckNSignaturesAddress
import Benchmarks.Safe.V0_cdb2eb5.CheckSignaturesAddress

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V0_cdb2eb5.safeChecknsignaturesBodyCore,
      ``Benchmarks.Safe.V0_cdb2eb5.safeChecksignaturesBodyCore,
      ``Benchmarks.Safe.V0_cdb2eb5.safeChecknsignaturesAddressBytes32BytesUint256BodyCore,
      ``Benchmarks.Safe.V0_cdb2eb5.safeChecksignaturesAddressBytes32BytesBodyCore] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
