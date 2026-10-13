import Benchmarks.CurveVault.TokenSetup
import Benchmarks.CurveVault.AddressWord
import Benchmarks.CurveVault.Storage
import Reasoning.ExternalCall
import Reasoning.SolmArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: converting a canonical address expression to a uint256 word.
theorem evalExpr_castAddressUint256_word {cfg : Config} {frame : Frame} {evm : State}
    {expr : Expr} {word : UInt256} (hcanon : word.toNat < EVM.addressModulus)
    (heval : evalExpr? cfg frame evm expr = .ok (.address (AccountAddress.ofNat word.toNat))) :
    evalExpr? cfg frame evm (.cast expr (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat word.toNat)) := by
  have ha : (AccountAddress.ofNat word.toNat).toNat = word.toNat := by
    change word.toNat % AccountAddress.size = word.toNat
    exact Nat.mod_eq_of_lt hcanon
  have hb : word.toNat < EVM.twoPow 256 := word.val.isLt
  rw [evalExpr?]
  simp only [heval, EvalResult.bind, bind, castValue?, ha, if_pos hb, EvalResult.ofOption]

def vaultTokenCallArgs (flow : VaultFlow) (amount : Expr) : List Expr :=
  [.storage {base := "_borrowed_token", steps := []},
    match flow with
    | .deposit | .mint => .cast (.env .caller) (.elem (.int (.uint ⟨256, by decide⟩)))
    | .withdraw | .redeem => .var "controller_word",
    match flow with
    | .deposit | .mint => .var "controller_word"
    | .withdraw | .redeem => .cast (.var "_receiver") (.elem (.int (.uint ⟨256, by decide⟩))),
    amount]

theorem vaultTokenCallArgs_eval (flow : VaultFlow) {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (locals : Store) (controller receiver amount : UInt256) (arg : Expr)
    (hbase : locals.get? "_borrowed_token" = none)
    (hc : locals.get? "controller_word" = some (.int (Int.ofNat controller.toNat)))
    (hr : locals.get? "_receiver" = some (.address (AccountAddress.ofNat receiver.toNat)))
    (hcanon : receiver.toNat < EVM.addressModulus)
    (ha : evalExpr? config {contract := contract, locals := locals} evm arg = .ok (.int (Int.ofNat amount.toNat))) :
    evalExprs? config {contract := contract, locals := locals} evm (vaultTokenCallArgs flow arg) =
      .ok [.address (AccountAddress.ofUInt256 (codeOwnerStorageWord I σ ⟨0⟩)),
        .int (Int.ofNat (vaultTokenFlowSender flow I controller).toNat),
        .int (Int.ofNat (vaultTokenFlowRecipient flow controller receiver).toNat), .int (Int.ofNat amount.toNat)] := by
  have htoken : evalExpr? config {contract := contract, locals := locals} evm
      (.storage {base := "_borrowed_token", steps := []}) =
      .ok (.address (AccountAddress.ofUInt256 (codeOwnerStorageWord I σ ⟨0⟩))) := by
    simpa only [wordToElem, hs.storageRead, accountAddress_ofUInt256_eq_ofNat_toNat] using
      vaultEvalScalar evm locals "_borrowed_token" .address ⟨0⟩ hbase rfl rfl
  have hcontroller := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) hc
  have hreceiver := evalExpr_castAddressUint256_word hcanon
    (show evalExpr? config {contract := contract, locals := locals} evm (.var "_receiver") = _ from by
      rw [evalExpr?]; simp only [hr, EvalResult.ofOption])
  have hcaller := evalExpr_castAddressUint256_word (addressWord_canonical I.source)
    (show evalExpr? config {contract := contract, locals := locals} evm (.env .caller) =
      .ok (.address (AccountAddress.ofNat (UInt256.ofNat I.source.val).toNat)) from by
      rw [addressWord_roundtrip, evalExpr?]; simp only [envValue, hs.env, pure])
  cases flow <;> simp only [vaultTokenCallArgs, vaultTokenFlowSender, vaultTokenFlowRecipient,
    evalExprs?, htoken, hcontroller, hreceiver, hcaller, ha, EvalResult.bind, bind, pure]

end Benchmarks.CurveVault
