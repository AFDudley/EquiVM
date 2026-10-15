import Benchmarks.Scaffolds.VestingWallet.Constructor
import Stele.Refine

/-!
# OpenZeppelin VestingWallet benchmark correctness stub

The source closure, optimized runtime bytecode, creation bytecode, storage layout, external ABI
model, and receive/SafeERC20 semantics are present. The runtime-equivalence proof is intentionally
left as the benchmark target.
-/

open Stele ABI Ethereum Ethereum.EVM

namespace OpenZeppelinBench.VestingWallet

theorem vestingWalletBenchCorrect :
    runtimeRefinement config vestingWalletBenchBytecode contract := by
  sorry

theorem vestingWalletBenchContractCorrect :
    contractRefinement config vestingWalletBenchCreationBytecode contract :=
  contractRefinement.of_constant vestingWalletBenchConstructorCorrect vestingWalletBenchCorrect

end OpenZeppelinBench.VestingWallet
