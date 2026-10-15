import Benchmarks.Safe.V3_77901a5.CheckNSignatures
import Benchmarks.Safe.V3_77901a5.CheckSignatures
import Benchmarks.Safe.V3_77901a5.CheckNSignaturesAddress
import Benchmarks.Safe.V3_77901a5.CheckSignaturesAddress

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V3_77901a5.safeChecknsignaturesBodyCore,
      ``Benchmarks.Safe.V3_77901a5.safeChecksignaturesBodyCore,
      ``Benchmarks.Safe.V3_77901a5.safeChecknsignaturesAddressBytes32BytesUint256BodyCore,
      ``Benchmarks.Safe.V3_77901a5.safeChecksignaturesAddressBytes32BytesBodyCore] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
