import Benchmarks.Morpho.MetaMorphoV1_1.SpecSyntax
open Benchmarks.Morpho.MetaMorphoV1_1
#eval Syntax.contractSyntax.functions.zipIdx.filterMap fun (f, i) =>
  if ["_accruedSupplyBalance", "_withdrawMorpho", "ERC4626__withdraw", "_withdraw", "_burn"].contains f.name
  then some (i, f.name) else none
