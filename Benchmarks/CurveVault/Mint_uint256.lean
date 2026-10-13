import Benchmarks.CurveVault.Dispatch

/-!
# Vault `mint(uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body (its own `calldatasize`/`callvalue` guard first), the Solm body evaluation, and the
`…Body` theorem `Correct.lean` consumes.
Dispatcher: bucket 2, arm entry pc 73; reach lemma `vaultReachMint_uint256Body`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch

namespace Benchmarks.CurveVault

set_option maxRecDepth 2000000

/-- `mint(uint256)`: the theorem `Correct.lean` routes selector 28 to. -/
theorem vaultMint_uint256Body {σ σ₀ A I} {g : UInt256}
    (hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 28)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 28) rfl hsel
  sorry

end Benchmarks.CurveVault
