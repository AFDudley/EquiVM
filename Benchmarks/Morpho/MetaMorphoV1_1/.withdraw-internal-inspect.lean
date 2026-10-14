import Benchmarks.Morpho.MetaMorphoV1_1.Spec
open Stele
open Benchmarks.Morpho.MetaMorphoV1_1
#eval contract.functions.zipIdx |>.filterMap fun (f, i) =>
  if f.name == "_burn" || f.name == "_withdraw" || f.name == "ERC4626__withdraw" then
    some (i, f.name, f.body)
  else none
