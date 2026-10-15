import Benchmarks.Safe.Main.CheckNSignatures
import Benchmarks.Safe.Main.CheckSignatures
import Benchmarks.Safe.Main.CheckNSignaturesAddress
import Benchmarks.Safe.Main.CheckSignaturesAddress

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.Main.safeChecknsignaturesBodyCore,
      ``Benchmarks.Safe.Main.safeChecksignaturesBodyCore,
      ``Benchmarks.Safe.Main.safeChecknsignaturesAddressBytes32BytesUint256BodyCore,
      ``Benchmarks.Safe.Main.safeChecksignaturesAddressBytes32BytesBodyCore] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
