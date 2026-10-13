import Benchmarks.EAS.EAS.EncodeAttestationSource
import Benchmarks.EAS.EAS.AllocateBlock
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- GENERALIZES Reasoning.Theory.encodePacked_uint256 to any nonzero ABI integer width.
theorem encodePacked_uint_width (w : UInt256) (width : ABI.BitWidth) (hne : width.val ≠ 0)
    (hfit : w.toNat < EVM.twoPow width.val) :
    encodePackedValue? (.elem (.int (.uint width))) (.int (Int.ofNat w.toNat)) =
      some (EVM.Word.toBytesBE w |>.drop (32-width.val/8)) := by
  have hw : EVM.word w.toNat = w := u256_ofNat_toNat w
  simp [encodePackedValue?,encodeABIWord?,hne,hfit,hw]

def getUIDPayload (a : AttestationRecord) (bump : UInt256) : ByteArray :=
  ⟨(EVM.Word.toBytesBE a.schema ++
    (EVM.Word.toBytesBE (UInt256.ofNat a.recipient.val)).drop 12 ++
    (EVM.Word.toBytesBE (UInt256.ofNat a.attester.val)).drop 12 ++
    (EVM.Word.toBytesBE a.time).drop 24 ++ (EVM.Word.toBytesBE a.expirationTime).drop 24 ++
    [if a.revocable then (1 : UInt8) else 0] ++ EVM.Word.toBytesBE a.refUID ++ a.data.toList ++
    (EVM.Word.toBytesBE bump).drop 28).toArray⟩
def getUIDWord (a : AttestationRecord) (bump : UInt256) : UInt256 := uInt256OfByteArray (KEC (getUIDPayload a bump))
def getUIDPackedArgs : List (ABIType × Expr) := [
  (abiBytes32,.field (.var "attestation") "schema"),
  (.elem .address,.field (.var "attestation") "recipient"),
  (.elem .address,.field (.var "attestation") "attester"),
  (.elem (.int (.uint ⟨64,by decide⟩)),.field (.var "attestation") "time"),
  (.elem (.int (.uint ⟨64,by decide⟩)),.field (.var "attestation") "expirationTime"),
  (.elem .bool,.field (.var "attestation") "revocable"),
  (abiBytes32,.field (.var "attestation") "refUID"),
  (.bytes,.field (.var "attestation") "data"),
  (.elem (.int (.uint ⟨32,by decide⟩)),.var "bump")]
def getUIDExpr : Expr := .keccak256 (.abiEncodePacked getUIDPackedArgs)

theorem getUIDExpr_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {a : AttestationRecord} {bump : UInt256}
    (ha : frame.locals.get? "attestation" = some a.value)
    (hb : frame.locals.get? "bump" = some (.int (Int.ofNat bump.toNat)))
    (ht : a.time.toNat < 2^64) (he : a.expirationTime.toNat < 2^64) (hc : bump.toNat < 2^32) :
    evalExpr? cfg frame evm getUIDExpr = .ok (wordBytes32Value (getUIDWord a bump)) := by
  have hp : evalPackedArgs? cfg frame evm getUIDPackedArgs = .ok (getUIDPayload a bump).toList := by
    change evalPackedArgs? cfg frame evm getUIDPackedArgs = _
    simp only [getUIDPayload,byteArray_toList_eq,List.toList_toArray,List.append_assoc]
    unfold getUIDPackedArgs
    apply evalPackedArgs_cons (attestationRecord_field ha "schema" _ rfl) (encodePacked_bytes32 _)
    apply evalPackedArgs_cons (attestationRecord_field ha "recipient" _ rfl) (by rfl)
    apply evalPackedArgs_cons (attestationRecord_field ha "attester" _ rfl) (by rfl)
    apply evalPackedArgs_cons (attestationRecord_field ha "time" _ rfl)
      (by simpa only [Nat.reduceDiv,Nat.reduceSub] using encodePacked_uint_width a.time ⟨64,by decide⟩ (by decide) ht)
    apply evalPackedArgs_cons (attestationRecord_field ha "expirationTime" _ rfl)
      (by simpa only [Nat.reduceDiv,Nat.reduceSub] using encodePacked_uint_width a.expirationTime ⟨64,by decide⟩ (by decide) he)
    apply evalPackedArgs_cons (attestationRecord_field ha "revocable" _ rfl) (by rfl)
    apply evalPackedArgs_cons (attestationRecord_field ha "refUID" _ rfl) (encodePacked_bytes32 _)
    apply evalPackedArgs_cons (attestationRecord_field ha "data" _ rfl) (by simp only [encodePackedValue?,byteArray_toList_eq])
    exact evalPackedArgs_single (v := .int (Int.ofNat bump.toNat)) (by simp only [evalExpr?,hb,EvalResult.ofOption])
      (by simpa only [Nat.reduceDiv,Nat.reduceSub] using encodePacked_uint_width bump ⟨32,by decide⟩ (by decide) hc)
  simp only [getUIDExpr,evalExpr?,hp,EvalResult.bind,bind,pure]
  simp only [wordBytes32Value,getUIDWord,toBytesBE_keccak_uInt256OfByteArray,byteArray_toList_eq,
    Array.toArray_toList]
  rfl

theorem getUIDPayload_size (a : AttestationRecord) (bump : UInt256) :
    (getUIDPayload a bump).size = 125+a.data.size := by
  have hw (w : UInt256) : (EVM.Word.toBytesBE w).length=32 := by simpa using word_toBytesBE_toByteArray_size w
  simp only [getUIDPayload,ByteArray.size,List.size_toArray,List.length_append,List.length_drop,hw,
    List.length_cons,List.length_nil,byteArray_toList_eq,Array.length_toList]
  change 121+a.data.data.size+4 = 125+a.data.data.size
  omega

abbrev getUIDFunction : FunctionDecl := contract.functions[24]!
def getUIDAllocateExpr : Expr := .binary .add (.intLit 157) (.arrayLength .localVar {base := "payload"})
def getUIDReturn : Body := [.return [getUIDExpr,.var "$EAS.freeMemory"],.return [.tupleLit [],.var "$EAS.freeMemory"]]
theorem getUID_body : getUIDFunction.body =
    [.letDecl "payload" (some .bytes) (.field (.var "attestation") "data")] ++ allocateBlock getUIDAllocateExpr ++ getUIDReturn := by native_decide

end Benchmarks.EAS.EAS
