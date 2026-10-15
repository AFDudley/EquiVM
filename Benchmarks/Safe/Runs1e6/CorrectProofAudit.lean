import Benchmarks.Safe.Runs1e6.Correct

open Lean Elab Command

run_cmd do
  for name in [``Benchmarks.Safe.Runs1e6.safeExectransactionBodyCore,
      ``Benchmarks.Safe.Runs1e6.safeConstructorCorrect, ``Benchmarks.Safe.Runs1e6.safeCorrect,
      ``Benchmarks.Safe.Runs1e6.safeContractCorrect] do
    let axioms ← Lean.collectAxioms name
    let standard := axioms.filter fun x ↦
      x == ``propext || x == ``Classical.choice || x == ``Quot.sound
    let native := axioms.filter fun x ↦ (x.toString.splitOn "native_decide.ax_").length > 1
    let unexpected := axioms.filter fun x ↦ !standard.contains x && !native.contains x
    if !unexpected.isEmpty then
      throwError "{name}: unexpected axioms {unexpected}"
    logInfo m!"{name}: {axioms.size} axioms; standard: {standard}; native: {native.size}; \
      unexpected: {unexpected}"
