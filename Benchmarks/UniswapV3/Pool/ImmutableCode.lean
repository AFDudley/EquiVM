import Benchmarks.UniswapV3.Pool.Bytecode
import Benchmarks.UniswapV3.Pool.Immutables
import Reasoning.Immutables

/-!
The patch sites of the deployed runtime template, keyed by Stele immutable name.  Generated
summaries quantify the words written at these sites; `Reasoning.Immutables.wordsOf` supplies them
from a Stele immutables store.
-/

open Reasoning.Immutables
open Benchmarks.UniswapV3.Pool.Immutables

namespace Benchmarks.UniswapV3.Pool

/-- Patch sites in the deployed runtime template. -/
def immutableLayout : Layout :=
  ⟨immutableReferences.flatMap (fun (name, sites) =>
    sites.map (fun offset => (offset, 32, name)))⟩

end Benchmarks.UniswapV3.Pool
