import Benchmarks.UniswapV4PoolManager.Bytecode
import Benchmarks.UniswapV4PoolManager.Immutables
import Reasoning.Immutables

/-!
The patch sites of the deployed runtime template, keyed by Stele immutable name.  Generated
summaries quantify the words written at these sites; `Reasoning.Immutables.wordsOf` supplies them
from a Stele immutables store.
-/

open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables

namespace Benchmarks.UniswapV4PoolManager

/-- Patch sites in the deployed runtime template. -/
def immutableLayout : Layout :=
  ⟨immutableReferences.flatMap (fun (name, sites) =>
    sites.map (fun offset => (offset, 32, name)))⟩

end Benchmarks.UniswapV4PoolManager
