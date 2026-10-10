import Benchmarks.EAS.EAS.AliasStorage
import Benchmarks.EAS.EAS.LowPacked
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def offchainAliasRoot (revoker : AccountAddress) : EvaledStorageRef :=
  {base := "_revocationsOffchain", steps := [.mindex (.address revoker)]}

def offchainAliasType : StorageType := .mapping (.bytes abiBytes32Width) (.elem (.int (.uint ⟨64, by decide⟩)))

def offchainRootRef : StorageRef := {base := "_revocationsOffchain", steps := [.mindex (.var "revoker")]}

def offchainAliasRef : StorageRef := {base := "revocations", steps := [.mindex (.var "data")]}

theorem offchain_root_resolve {evm : EVM.State} {locals imms : Store} {revoker : AccountAddress}
    (hnone : locals.get? "_revocationsOffchain" = none)
    (hwho : locals.get? "revoker" = some (.address revoker)) :
    resolveStorageRef? config {contract := contract, locals := locals, immutables := imms} evm offchainRootRef =
      .ok (offchainAliasRoot revoker, offchainAliasType) := by
  refine resolveStorageRef?_ok hnone ?_ rfl
  simp only [evalStorageRef, offchainRootRef, evalStorageRefSteps, evalStorageRefStep,
    evalExpr?, hwho, EvalResult.ofOption, valueToKey?, pure, bind, EvalResult.bind]
  rfl

theorem offchain_alias_resolve {evm : EVM.State} {locals imms : Store} {revoker : AccountAddress} {word : UInt256}
    (halias : locals.get? "revocations" = some (.storageRef (offchainAliasRoot revoker) offchainAliasType))
    (hkey : locals.get? "data" = some (wordBytes32Value word)) :
    resolveStorageRef? config {contract := contract, locals := locals, immutables := imms} evm offchainAliasRef =
      .ok (offchainEvaledRef revoker word, .elem (.int (.uint ⟨64, by decide⟩))) := by
  have hlen : (EVM.Word.toBytesBE word).length = 32 := by simpa using word_toBytesBE_toByteArray_size word
  simp only [resolveStorageRef?, offchainAliasRef, halias, evalStorageRefFrom?, evalStorageRefStep,
    evalExpr?, hkey, wordBytes32Value, EvalResult.ofOption, valueToKey?, hlen, abiBytes32Width,
    show (31 : Nat) + 1 = 32 from rfl, if_true, pure, bind, EvalResult.bind]
  rfl


def offchainStore (evm : EVM.State) (revoker : AccountAddress) (word time : UInt256) : EVM.State :=
  EVM.storageStore evm evm.executionEnv.codeOwner (offchainSlot (keyValueToWord (.address revoker)) word)
    (setLowWord (EVM.storageLoad evm evm.executionEnv.codeOwner
      (offchainSlot (keyValueToWord (.address revoker)) word)) time 64)

theorem offchain_alias_read {evm : EVM.State} {locals imms : Store} {revoker : AccountAddress} {word : UInt256}
    (halias : locals.get? "revocations" = some (.storageRef (offchainAliasRoot revoker) offchainAliasType))
    (hkey : locals.get? "data" = some (wordBytes32Value word)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (.storage offchainAliasRef) = .ok (.int (Int.ofNat (offchainWord evm revoker word).toNat)) := by
  exact evalExpr_storage_resolved_value (loc := offchainLoc revoker word)
    (offchain_alias_resolve halias hkey) easStorageBackend (offchain_layout revoker word)
    (storageLocLoad_uint_offset0 evm (offchainSlot (keyValueToWord (.address revoker)) word)
      8 ⟨64, by decide⟩ rfl (by decide))

theorem offchain_alias_write {evm : EVM.State} {locals imms : Store} {revoker : AccountAddress} {word time : UInt256}
    (halias : locals.get? "revocations" = some (.storageRef (offchainAliasRoot revoker) offchainAliasType))
    (hkey : locals.get? "data" = some (wordBytes32Value word)) :
    assignStorageRef? config {contract := contract, locals := locals, immutables := imms} evm
      .storage offchainAliasRef (.int (Int.ofNat time.toNat)) =
      .ok ({contract := contract, locals := locals, immutables := imms}, offchainStore evm revoker word time) := by
  exact assignStorageRef_resolved_value (loc := offchainLoc revoker word)
    (offchain_alias_resolve halias hkey) easStorageBackend (offchain_layout revoker word) (Or.inl ⟨_, rfl⟩)
    (storageLocStore_uint_offset0_word evm (offchainSlot (keyValueToWord (.address revoker)) word)
      time 8 ⟨64, by decide⟩ rfl (by decide))

end Benchmarks.EAS.EAS
