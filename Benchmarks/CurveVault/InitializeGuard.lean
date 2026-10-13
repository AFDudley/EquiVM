import Benchmarks.CurveVault.InitializeStorage
import Benchmarks.CurveVault.InitializeLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultInitializeGuardExpr : Expr :=
  .binary .eq (.storage {base := "_borrowed_token", steps := []}) (.cast (.intLit 0) (.elem .address))

theorem vaultInitializeGuardEval (evm : State) (locals : Store)
    (hbase : locals.get? "_borrowed_token" = none)
    (hcanon : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat < EVM.addressModulus) :
    evalExpr? config {contract := contract, locals := locals} evm vaultInitializeGuardExpr =
      .ok (.bool (decide (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩))) := by
  have he := vaultEvalScalar evm locals "_borrowed_token" .address ⟨0⟩ hbase rfl rfl
  change evalExpr? config {contract := contract, locals := locals} evm
    (.storage {base := "_borrowed_token", steps := []}) =
    .ok (.address (AccountAddress.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat)) at he
  rw [vaultInitializeGuardExpr, evalExpr_binary_nonshort (by decide) (by decide), he]
  have hz : evalExpr? config {contract := contract, locals := locals} evm
      (.cast (.intLit 0) (.elem .address)) = .ok (.address (AccountAddress.ofNat 0)) := by
    simp only [evalExpr?, EvalResult.bind, bind, pure, castValue?, EvalResult.ofOption]; rfl
  rw [hz]
  simp only [EvalResult.bind, bind, evalBinaryOp?, value_address_beq]
  simp only [addressOfWord_eq_iff hcanon (AccountAddress.ofNat 0)]
  rfl

end Benchmarks.CurveVault
