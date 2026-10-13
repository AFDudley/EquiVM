import Benchmarks.Morpho.MorphoBlue.Bytecode
import Benchmarks.Morpho.MorphoBlue.Immutables
import Reasoning.Immutables

/-!
The patch sites of the deployed runtime template, keyed by Stele immutable name.  Generated
summaries quantify the words written at these sites; `Reasoning.Immutables.wordsOf` supplies them
from a Stele immutables store.
-/

open Reasoning.Immutables
open Benchmarks.Morpho.MorphoBlue.Immutables

namespace Benchmarks.Morpho.MorphoBlue

/-- Patch sites in the deployed runtime template. -/
def immutableLayout : Layout :=
  ⟨immutableReferences.flatMap (fun (name, sites) =>
    sites.map (fun offset => (offset, 32, name)))⟩

end Benchmarks.Morpho.MorphoBlue
