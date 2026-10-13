import Benchmarks.EAS.EAS.MultiDelegatedAttestSource
import Benchmarks.EAS.EAS.DelegatedAttestationBatch
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

abbrev checkAttestationCopyFunction : FunctionDecl := contract.functions[8]!
def checkAttestationCopyWord (e : Expr) (name : Ident) : Body :=
  heapResultBlock "_calldataWord" [e,.var "$EAS.freeMemory"] (name++"$allocation") name "$EAS.freeMemory"
def checkAttestationCopyCast (e : Expr) : Expr := .cast e (.elem (.int abiUInt256Int))
def checkAttestationCopySlot (base index : Ident) : Expr := checkAttestationCopyCast
  (.binary .add (.var base) (.binary .mul (.var index) (.intLit 32)))
def checkAttestationCopyPrefix : Body := [
  .letDecl "input" (some .bytes) (.env .msgData)] ++
  checkAttestationCopyWord (.intLit 4) "root" ++ [
  .letDecl "heads" (some abiUInt256) (checkAttestationCopyCast (.binary .add (.var "root") (.intLit 36)))] ++
  checkAttestationCopyWord (checkAttestationCopySlot "heads" "index") "relative" ++ [
  .letDecl "request" (some abiUInt256) (checkAttestationCopyCast (.binary .add (.var "heads") (.var "relative")))] ++
  checkAttestationCopyWord (checkAttestationCopyCast (.binary .add (.var "request") (.intLit 32))) "tail" ++ [
  .letDecl "data" (some abiUInt256) (checkAttestationCopyCast (.binary .add (.binary .add (.var "request") (.var "tail")) (.intLit 32)))]
def checkAttestationCopyExtent : Stmt := .require (.binary .le (checkAttestationCopySlot "data" "length")
  (checkAttestationCopyCast (.arrayLength .localVar {base := "input"})))
def checkAttestationCopyGuard : Expr := .binary .lt (.var "i") (.var "length")
def checkAttestationCopyOffset : Stmt := .require (.binary .le (.var "offset") (.intLit (2^64-1)))
def checkAttestationCopyIteration : Body := checkAttestationCopyWord (checkAttestationCopySlot "data" "i") "offset" ++
  [checkAttestationCopyOffset,localCastIncrement "i"]
def checkAttestationCopyLoop : Stmt := .while checkAttestationCopyGuard checkAttestationCopyIteration

theorem checkAttestationCopy_body : checkAttestationCopyFunction.body=checkAttestationCopyPrefix++
    [checkAttestationCopyExtent,.letDecl "i" (some abiUInt256) (.intLit 0),checkAttestationCopyLoop]++copyRequestReturn := by native_decide

def checkAttestationCopyBase (cd : ByteArray) : UInt256 := UInt256.ofNat ((calldataWord cd 4).toNat+36)
def checkAttestationCopyRoot (cd : ByteArray) (index : Nat) : UInt256 := checkAttestationCopyBase cd+
  calldataWord cd (UInt256.ofNat ((checkAttestationCopyBase cd).toNat+32*index)).toNat
def checkAttestationCopyData (cd : ByteArray) (index : Nat) : UInt256 :=
  delegatedAttestationDataOffset cd (checkAttestationCopyRoot cd index)

end Benchmarks.EAS.EAS
