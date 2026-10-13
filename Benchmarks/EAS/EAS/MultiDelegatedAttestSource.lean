import Benchmarks.EAS.EAS.MultiAttestSource
import Benchmarks.EAS.EAS.BatchRowRead
import Benchmarks.EAS.EAS.DelegatedAttestationFacts
import Benchmarks.EAS.EAS.VerifyAttestRun
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiDelegatedAttestLength : Expr := .arrayLength .localVar {base := "multiDelegatedRequests"}
def multiDelegatedAttestInitial : Body := [
  .letDecl "totalUids" (some (.dynamicArray (.dynamicArray abiBytes32))) (.newArray (.dynamicArray (.elem (.bytes abiBytes32Width))) multiDelegatedAttestLength),
  .letDecl "totalUidsCount" (some abiUInt256) (.intLit 0),
  .letDecl "availableValue" (some abiUInt256) (.env .callvalue),.letDecl "i" (some abiUInt256) (.intLit 0)]
def multiDelegatedAttestAllocate : Body := arrayAllocateExprBlock multiDelegatedAttestLength 32 ++ multiDelegatedAttestInitial

def multiDelegatedAttestRead : Body := batchRowRead DelegatedBatchSite.attest.abi "multiDelegatedRequests" "multiDelegatedRequest"
def multiDelegatedAttestCheck (name : Ident) : Stmt :=
  .require (.binary .ne (.var name) (.structLit "$solc08Calldata.decodeFailure" []))
def multiDelegatedAttestFields : Body := [
  .letDecl "data" (some (.dynamicArray requestDataABI)) (.tupleGet (.var "multiDelegatedRequest") 1),
  multiDelegatedAttestCheck "data",
  .require (.binary .ne (.arrayLength .localVar {base := "data"}) (.intLit 0)),
  .letDecl "signatures" (some (.dynamicArray signatureABI)) (.tupleGet (.var "multiDelegatedRequest") 2),
  multiDelegatedAttestCheck "signatures",
  .require (.binary .eq (.arrayLength .localVar {base := "data"}) (.arrayLength .localVar {base := "signatures"})),
  .letDecl "j" (some abiUInt256) (.intLit 0)]
def multiDelegatedAttestPrepare : Body := multiDelegatedAttestRead ++ [multiDelegatedAttestCheck "multiDelegatedRequest"] ++ multiDelegatedAttestFields

def multiDelegatedAttestDatumRead : Body := [
  .letDecl "datum" (some requestDataABI) (.index (.var "data") (.var "j")),
  .letDecl "signature" (some signatureABI) (.index (.var "signatures") (.var "j")),
  .letDecl "attester" (some (.elem .address)) (.tupleGet (.var "multiDelegatedRequest") 3)]
def multiDelegatedAttestDatumChecks : Body :=
  [multiDelegatedAttestCheck "datum",multiDelegatedAttestCheck "attester",multiDelegatedAttestCheck "signature"]
def multiDelegatedAttestDatumCopy : Body := heapResultBlock "_copyAttestationData" [.var "datum",.var "$EAS.freeMemory"]
  "allocation$allocation" "allocation" "$EAS.freeMemory"
def multiDelegatedAttestVerifyArgs : List Expr := [
  .structLit "DelegatedAttestationRequest" [
    ("schema",.tupleGet (.var "multiDelegatedRequest") 0),("data",.var "datum"),
    ("signature",.var "signature"),("attester",.var "attester")],.var "$EAS.freeMemory"]
def multiDelegatedAttestVerify : Body := heapResultBlock "_verifyAttest" multiDelegatedAttestVerifyArgs
  "__c0$allocation" "__c0" "$EAS.freeMemory"
def multiDelegatedAttestDatumPrepare : Body := multiDelegatedAttestDatumRead ++ multiDelegatedAttestDatumChecks ++
  allocateBlock (.intLit 128) ++ multiDelegatedAttestDatumCopy ++ allocateBlock (.intLit 96)
def multiDelegatedAttestVerifyIteration : Body := multiDelegatedAttestDatumPrepare ++ multiDelegatedAttestVerify ++ [localCastIncrement "j"]
def multiDelegatedAttestCopyCheckArgs : List Expr := [.var "i",.arrayLength .localVar {base := "data"},.var "$EAS.freeMemory"]
def multiDelegatedAttestCopyCheck : Body := heapResultBlock "_checkAttestationArrayCopy" multiDelegatedAttestCopyCheckArgs
  "__copyCheck$allocation" "__copyCheck" "$EAS.freeMemory"
def multiDelegatedAttestArrayCopy : Body := heapResultBlock "_copyAttestationArray" [.var "data",.var "$EAS.freeMemory"]
  "allocation$allocation" "allocation" "$EAS.freeMemory"
def multiDelegatedAttestCallArgs : List Expr := [
  .tupleGet (.var "multiDelegatedRequest") 0,.var "data",.tupleGet (.var "multiDelegatedRequest") 3,
  .var "availableValue",.var "last",.var "$EAS.freeMemory"]
def multiDelegatedAttestCall : Body := heapResultBlock "_attest" multiDelegatedAttestCallArgs "res$allocation" "res" "$EAS.freeMemory"
def multiDelegatedAttestIteration : Body := multiDelegatedAttestPrepare ++
  [.while (localArrayGuard "j" "data") multiDelegatedAttestVerifyIteration] ++ multiDelegatedAttestCopyCheck ++
  multiDelegatedAttestArrayCopy ++ multiDelegatedAttestCall ++ multiAttestUpdate
def multiDelegatedAttestFinish : Body := heapResultBlock "_mergeUIDs" multiAttestMergeArgs "__c2$allocation" "__c2" "$EAS.freeMemory" ++
  [.return [(.var "__c2")]]

theorem multiDelegatedAttest_body : multiAttestByDelegationTransition.body = easPayableEntryPrefix ++ multiDelegatedAttestAllocate ++
    [.while (localArrayGuard "i" "multiDelegatedRequests") multiDelegatedAttestIteration] ++ multiDelegatedAttestFinish := by native_decide

end Benchmarks.EAS.EAS
