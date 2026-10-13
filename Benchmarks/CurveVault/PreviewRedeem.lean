import Benchmarks.CurveVault.Dispatch

/-!
# Vault `previewRedeem(uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body (its own `calldatasize`/`callvalue` guard first), the Solm body evaluation, and the
`…Body` theorem `Correct.lean` consumes.
Dispatcher: bucket 3, arm entry pc 73; reach lemma `vaultReachPreviewRedeemBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch

namespace Benchmarks.CurveVault

set_option maxRecDepth 2000000

/-- `previewRedeem(uint256)`: the theorem `Correct.lean` routes selector 18 to. -/
theorem vaultPreviewRedeemBody {σ σ₀ A I} {g : UInt256}
    (hwf : storageWF σ I)
    (hcode : I.code = vaultBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vaultSelBytes 18)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 18) rfl hsel
  sorry

end Benchmarks.CurveVault
