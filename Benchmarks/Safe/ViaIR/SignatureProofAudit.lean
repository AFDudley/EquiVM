import Benchmarks.Safe.ViaIR.CheckNSignatures
import Benchmarks.Safe.ViaIR.CheckSignatures
import Benchmarks.Safe.ViaIR.CheckNSignaturesAddress
import Benchmarks.Safe.ViaIR.CheckSignaturesAddress

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.ViaIR.safeChecknsignaturesBodyCore,
      ``Benchmarks.Safe.ViaIR.safeChecksignaturesBodyCore,
      ``Benchmarks.Safe.ViaIR.safeChecknsignaturesAddressBytes32BytesUint256BodyCore,
      ``Benchmarks.Safe.ViaIR.safeChecksignaturesAddressBytes32BytesBodyCore] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun x ↦ x != ``propext && x != ``Classical.choice &&
      x != ``Quot.sound && !((x.toString.splitOn "native_decide.ax_").length > 1)
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; unexpected: {unexpected}"
