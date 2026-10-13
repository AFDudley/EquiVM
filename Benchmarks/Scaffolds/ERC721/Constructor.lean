import Benchmarks.Scaffolds.ERC721.Bytecode
import Stele.Refine

/-!
# ERC721 constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Stele constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Stele ABI Ethereum Ethereum.EVM

namespace ERC721

theorem erc721ConstructorCorrect :
    typedConstructorRefinement erc721Config erc721CreationBytecode erc721Contract (fun _ => erc721Bytecode) := by
  sorry

end ERC721
