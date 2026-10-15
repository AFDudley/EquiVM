import Benchmarks.EAS.EAS.TryRecoverExpr
import Benchmarks.EAS.EAS.HeapResultBlock
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def easCtorName : UInt256 := uInt256OfByteArray (KEC "EAS".toUTF8)
def easCtorVersion : UInt256 := uInt256OfByteArray (KEC "0.26".toUTF8)
def easCtorType : UInt256 := uInt256OfByteArray (KEC "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)".toUTF8)
def easCtorDomain (owner : AccountAddress) : UInt256 := builtDomainWord easCtorType easCtorName easCtorVersion owner

def easCtorArgs (registry : AccountAddress) : Store := Std.HashMap.ofList [("registry",.address registry)]
def easCtorHashLocals (L : Store) : Store :=
  ((L.insert "$EAS.freeMemory" (.int 512)).insert "hashedName" (wordBytes32Value easCtorName)).insert
    "hashedVersion" (wordBytes32Value easCtorVersion) |>.insert "typeHash" (wordBytes32Value easCtorType)
def easCtorImms1 (imms : Store) : Store :=
  (imms.insert "_HASHED_NAME" (.int (Int.ofNat easCtorName.toNat))).insert "_HASHED_VERSION" (.int (Int.ofNat easCtorVersion.toNat))
    |>.insert "_CACHED_CHAIN_ID" (.int (Int.ofNat Ethereum.chainId))
def easCtorImms2 (imms : Store) (owner : AccountAddress) : Store :=
  ((easCtorImms1 imms).insert "_CACHED_DOMAIN_SEPARATOR" (.int (Int.ofNat (easCtorDomain owner).toNat))).insert
    "_CACHED_THIS" (.address owner) |>.insert "_TYPE_HASH" (.int (Int.ofNat easCtorType.toNat))
def easCtorImms (owner registry : AccountAddress) : Store :=
  (easCtorImms2 (initialImmutables contract) owner).insert "_schemaRegistry" (.address registry)
def easCtorLocals (L : Store) (owner : AccountAddress) : Store :=
  heapResultLocals (easCtorHashLocals L) "domain$allocation" "domain" "$EAS.freeMemory" (wordBytes32Value (easCtorDomain owner)) 704

def easCtorPrefix : Body := [
  .letDecl "$EAS.freeMemory" none (.intLit 512),.require (.binary .eq (.env .callvalue) (.intLit 0)),
  .letDecl "hashedName" (some abiBytes32) (.keccak256 (.bytesLit "EAS".toUTF8)),
  .letDecl "hashedVersion" (some abiBytes32) (.keccak256 (.bytesLit "0.26".toUTF8)),
  .letDecl "typeHash" (some abiBytes32) (.keccak256 (.bytesLit "EIP712Domain(string name,string version,uint256 chainId,address verifyingContract)".toUTF8)),
  .setImmutable "_HASHED_NAME" (.cast (.var "hashedName") (.elem (.int (.uint ⟨256,by decide⟩)))),
  .setImmutable "_HASHED_VERSION" (.cast (.var "hashedVersion") (.elem (.int (.uint ⟨256,by decide⟩)))),
  .setImmutable "_CACHED_CHAIN_ID" (.env .chainid)]
def easCtorDomainArgs : List Expr := [.var "typeHash",.var "hashedName",.var "hashedVersion",.var "$EAS.freeMemory"]
def easCtorDomainBlock : Body := heapResultBlock "_buildDomainSeparator" easCtorDomainArgs "domain$allocation" "domain" "$EAS.freeMemory"
def easCtorSetDomain : Body := [
  .setImmutable "_CACHED_DOMAIN_SEPARATOR" (.cast (.var "domain") (.elem (.int (.uint ⟨256,by decide⟩)))),
  .setImmutable "_CACHED_THIS" (.env .this),
  .setImmutable "_TYPE_HASH" (.cast (.var "typeHash") (.elem (.int (.uint ⟨256,by decide⟩))))]
def easCtorGuard : Expr := .binary .ne (.var "registry") (.cast (.intLit 0) (.elem .address))
def easCtorFinish : Body := [.require easCtorGuard,.setImmutable "_schemaRegistry" (.var "registry")]

theorem easCtorBody : contract.ctor.body = easCtorPrefix ++ easCtorDomainBlock ++ easCtorSetDomain ++ easCtorFinish := by native_decide

theorem easCtorDeployment_shape {args : List Value} {code : ByteArray}
    (hd : config.selfDeployment easCreationBytecode args = some code) :
    ∃ registry : AccountAddress, args = [.address registry] ∧ code = easCreationBytecode ++ (UInt256.ofNat registry.val).toByteArray := by
  change (do
    let bytes ← encodeABIValues? [.elem .address] args
    pure (easCreationBytecode ++ bytes.toByteArray)) = some code at hd
  cases args with
  | nil => simp [encodeABIValues?,encodeABIValuesFrom?,abiTupleHeadSize?] at hd
  | cons arg rest =>
    cases rest with
    | cons arg2 rest => simp [encodeABIValues?,encodeABIValuesFrom?,abiTupleHeadSize?,staticABIEncodedSize?,isDynamicABIType] at hd
    | nil =>
      cases arg <;>
        simp only [encodeABIValues?,encodeABIValuesFrom?,abiTupleHeadSize?,staticABIEncodedSize?,isDynamicABIType,
          encodeABIValue?,encodeABIWord?,bind,Option.bind,pure,if_false,Option.some.injEq,List.append_nil,List.nil_append,reduceCtorEq] at hd
      rename_i registry
      exact ⟨registry,rfl,by simpa only [word_toBytesBE_toByteArray_eq_toByteArray] using hd.symm⟩

-- LIBRARY CANDIDATE: the source hash of literal bytes agrees with the EVM hash word.
theorem evalKeccakLiteral {cfg : Config} {frame : Frame} {evm : EVM.State} (bytes : ByteArray) :
    evalExpr? cfg frame evm (.keccak256 (.bytesLit bytes)) = .ok (wordBytes32Value (uInt256OfByteArray (KEC bytes))) := by
  simp only [evalExpr?,EvalResult.bind,bind,pure,wordBytes32Value,toBytesBE_keccak_uInt256OfByteArray]
  rfl

end Benchmarks.EAS.EAS
