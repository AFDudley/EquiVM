import Benchmarks.CurveVault.Common

/-!
# Vault constructor correctness

Creation-code equivalence: the constructor's EVM trace (argument decode, stores, runtime-code
return) against the Solm constructor body, composed from the creation summaries.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CurveVault

theorem vaultConstructorCorrect :
    typedConstructorRefinement config vaultCreationBytecode contract (fun _ => vaultBytecode) := by
  sorry

end Benchmarks.CurveVault
