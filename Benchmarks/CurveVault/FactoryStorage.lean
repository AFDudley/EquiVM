import Benchmarks.CurveVault.Storage
import Benchmarks.CurveVault.Calls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

theorem vaultFactoryEval (evm : State) (locals : Store) (hbase : locals.get? "_factory" = none) :
    evalExpr? config {contract := contract, locals := locals} evm (.storage {base := "_factory", steps := []}) =
      .ok (.address (AccountAddress.ofUInt256 (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩))) := by
  rw [accountAddress_ofUInt256_eq_ofNat_toNat]
  exact vaultEvalScalar evm locals "_factory" .address ⟨4⟩ hbase rfl rfl

theorem vaultAdminCalldata (mem : ByteArray) :
    config.externalABI.encode? "admin" [] = some
      (((UInt256.ofNat 4166100032).toByteArray.write 0 mem 64 32).readWithPadding 92 4) := by
  change ABI.encodeCallWithSelector? (selectorBytes 0xf8 0x51 0xa4 0x40) [] [] = _
  exact vyperNullaryCallData _ _ mem 64 (by decide +kernel)
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 64 (by norm_num)))

end Benchmarks.CurveVault
