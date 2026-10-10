import Benchmarks.EAS.EAS.MultiAttestSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def multiAttestReadLocals (L : Store) (last : Bool) (row : Value) : Store :=
  (L.insert "last" (.bool false)).insert "last" (.bool last) |>.insert "multiRequest" row

def multiRequestRead (ty : ABIType) : Body := [
  .letDecl "last" (some (.elem .bool)) (.boolLit false),
  .assign .localVar {base := "last"} multiAttestLast,
  .letDecl "multiRequest" (some ty) (.index (.var "multiRequests") (.var "i"))]

-- LIBRARY CANDIDATE: read one batch row and compute the last-row flag, independent of row type.
theorem multiRequestReadSource {L imms : Store} {evm : EVM.State} {requests : List Value}
    {i : Nat} (ty : ABIType)
    (hrequests : L.get? "multiRequests" = some (.array requests))
    (hindex : L.get? "i" = some (.int (Int.ofNat i))) (hi : i < requests.length)
    (hlen : requests.length < UInt256.size) (hnorm : normalizeRawBoolWord? requests[i] = .ok requests[i]) :
    ExecBlock config {contract := contract,locals := L,immutables := imms} evm (multiRequestRead ty)
      (.ok {contract := contract,locals := multiAttestReadLocals L (decide (i=requests.length-1)) requests[i],immutables := imms} evm) := by
  let L1 := L.insert "last" (.bool false)
  have hn : (UInt256.ofNat requests.length).toNat = requests.length := ulit_toNat' _ hlen
  have hs : (UInt256.sub (UInt256.ofNat requests.length) (UInt256.ofNat 1)).toNat = requests.length-1 := by
    rw [usub_toNat (by rw [hn]; change 1 ≤ requests.length; omega),hn]
    rfl
  have hi1 : L1.get? "i" = some (.int (Int.ofNat i)) := by simpa (disch := decide) only [L1,store_get_ne] using hindex
  have hd1 : L1.get? "multiRequests" = some (.array requests) := by simpa (disch := decide) only [L1,store_get_ne] using hrequests
  have he := evalCastUint256Sub (cfg := config) (frame := {contract := contract,locals := L1,immutables := imms}) (evm := evm)
    (a := multiAttestLength) (b := .intLit 1) (x := UInt256.ofNat requests.length) (y := UInt256.ofNat 1)
    (by rw [hn]; exact evalLocalArrayLength hd1) (by simp only [evalExpr?,pure]; rfl)
    (by rw [hn]; change 1 ≤ requests.length; omega)
  have hlast : evalExpr? config {contract := contract,locals := L1,immutables := imms} evm multiAttestLast =
      .ok (.bool (decide (i=requests.length-1))) := by
    have hv : (Value.int (Int.ofNat i) == Value.int (Int.ofNat (requests.length-1))) = decide (i=requests.length-1) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq,Value.int.injEq,Int.ofNat_eq_natCast,Nat.cast_inj,decide_eq_true_eq]
    rw [multiAttestLast,evalExpr?,evalLocalValue hi1,he] <;> try decide
    simp only [bind,EvalResult.bind,hs,evalBinaryOp_eq_int_ok,hv]
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := .bool false) (by simp only [evalExpr?,pure]))
  apply ExecBlock.consNormal (ExecStmt.assign hlast (assignLocalValue (store_get_self L "last" (.bool false))))
  apply ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil
  apply evalArrayIndex
    (evalLocalValue (by simpa (disch := decide) only [store_get_ne] using hd1))
    (evalLocalValue (by simpa (disch := decide) only [store_get_ne] using hi1)) hi rfl hnorm

theorem multiRequestCheck_ok {L imms : Store} {evm : EVM.State} {fields : List Value}
    (h : L.get? "multiRequest" = some (.tuple fields)) :
    ExecStmt config {contract := contract,locals := L,immutables := imms} evm multiAttestCheck
      (.ok {contract := contract,locals := L,immutables := imms} evm) := by
  apply ExecStmt.requireTrue
  simp only [evalExpr?,h,EvalResult.ofOption,bind,EvalResult.bind,pure,evalStructFields?,multiAttestCheck]
  rfl

theorem multiRequestCheck_bad {L imms : Store} {evm : EVM.State}
    (h : L.get? "multiRequest" = some ABI.Solc08Calldata.decodeFailure) :
    ExecStmt config {contract := contract,locals := L,immutables := imms} evm multiAttestCheck .reverted := by
  apply ExecStmt.requireFalse
  simp only [evalExpr?,h,EvalResult.ofOption,bind,EvalResult.bind,pure,evalStructFields?,multiAttestCheck]
  rfl

end Benchmarks.EAS.EAS
