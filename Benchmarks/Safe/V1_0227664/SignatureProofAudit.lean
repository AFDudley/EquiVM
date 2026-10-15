import Benchmarks.Safe.V1_0227664.CheckNSignatures
import Benchmarks.Safe.V1_0227664.CheckSignatures
import Benchmarks.Safe.V1_0227664.CheckNSignaturesAddress
import Benchmarks.Safe.V1_0227664.CheckSignaturesAddress

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.V1_0227664.safeChecknsignaturesBodyCore,
      ``Benchmarks.Safe.V1_0227664.safeChecksignaturesBodyCore,
      ``Benchmarks.Safe.V1_0227664.safeChecknsignaturesAddressBytes32BytesUint256BodyCore,
      ``Benchmarks.Safe.V1_0227664.safeChecksignaturesAddressBytes32BytesBodyCore] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
