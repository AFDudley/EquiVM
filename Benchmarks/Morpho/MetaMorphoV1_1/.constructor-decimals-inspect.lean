import Benchmarks.Morpho.MetaMorphoV1_1.SpecSyntax

open Stele Benchmarks.Morpho.MetaMorphoV1_1.Syntax

#eval contractSyntax.functions.zipIdx |>.filterMap fun (fn, i) =>
  if fn.name == "_tryGetAssetDecimals" then some (i, fn.params, fn.returnType, fn.body) else none
#eval contractSyntax.ctor.body.take 5
