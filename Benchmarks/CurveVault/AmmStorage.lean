import Benchmarks.CurveVault.Storage

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

theorem vaultAmmEval (evm : EVM.State) (locals : Store) (hbase : locals.get? "_amm" = none) :
    evalExpr? config {contract := contract, locals := locals} evm (.storage {base := "_amm", steps := []}) =
      .ok (.address (AccountAddress.ofUInt256 (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩))) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  exact vaultEvalScalar evm locals "_amm" .address ⟨2⟩ hbase rfl rfl
end Benchmarks.CurveVault
