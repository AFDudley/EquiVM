import Benchmarks.EAS.EAS.RecordEncoding
import Benchmarks.EAS.EAS.TimeArray
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: a byte-array form of the packed-expression evaluation rule.
theorem evalPackedBytes {cfg : Config} {frame : Frame} {evm : EVM.State}
    {args : List (ABIType × Expr)} {out : ByteArray}
    (h : evalPackedArgs? cfg frame evm args = .ok out.toList) :
    evalExpr? cfg frame evm (.abiEncodePacked args) = .ok (.bytes out) := by
  simp only [evalExpr?, h, EvalResult.bind, bind, pure]
  apply congrArg (fun b => EvalResult.ok (Value.bytes b))
  exact byteArray_eq_of_toList_eq (by simp only [byteArray_toList_eq, List.toList_toArray])

-- LIBRARY CANDIDATE: concatenate dynamic ABI elements and list their relative offsets.
def dynamicBodies : List ByteArray → ByteArray
  | [] => .empty
  | b :: bs => b ++ dynamicBodies bs

def dynamicOffsets (start : Nat) : List ByteArray → List UInt256
  | [] => []
  | b :: bs => UInt256.ofNat start :: dynamicOffsets (start+b.size) bs

theorem dynamicBodies_append (xs ys : List ByteArray) :
    dynamicBodies (xs ++ ys) = dynamicBodies xs ++ dynamicBodies ys := by
  induction xs with
  | nil => simp only [dynamicBodies, List.nil_append, ByteArray.empty_append]
  | cons x xs ih => simp only [List.cons_append, dynamicBodies, ih, ByteArray.append_assoc]

theorem dynamicOffsets_append (start : Nat) (xs ys : List ByteArray) :
    dynamicOffsets start (xs ++ ys) = dynamicOffsets start xs ++
      dynamicOffsets (start+(dynamicBodies xs).size) ys := by
  induction xs generalizing start with
  | nil => simp only [List.nil_append, dynamicOffsets, dynamicBodies, ByteArray.size_empty, Nat.add_zero]
  | cons x xs ih => simp only [List.cons_append, dynamicOffsets, ih, dynamicBodies,
      ByteArray.size_append, Nat.add_assoc]

theorem dynamicOffsets_length (start : Nat) (xs : List ByteArray) :
    (dynamicOffsets start xs).length = xs.length := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih => simp only [dynamicOffsets, List.length_cons, ih]

theorem dynamicBodies_take_size_le (xs : List ByteArray) (i : Nat) :
    (dynamicBodies (xs.take i)).size ≤ (dynamicBodies xs).size := by
  have h := congrArg ByteArray.size (dynamicBodies_append (xs.take i) (xs.drop i))
  rw [List.take_append_drop, ByteArray.size_append] at h
  omega

def attestationArrayBodies (ats : List AttestationRecord) (i : Nat) : ByteArray :=
  dynamicBodies ((ats.take i).map AttestationRecord.encoding)

def attestationArrayHeads (ats : List AttestationRecord) (i : Nat) : List UInt256 :=
  dynamicOffsets (32*ats.length) ((ats.take i).map AttestationRecord.encoding)

def attestationArrayOffset (ats : List AttestationRecord) (i : Nat) : Nat :=
  32*ats.length+(attestationArrayBodies ats i).size

def attestationArrayEncoding (ats : List AttestationRecord) : ByteArray :=
  wordBytes (UInt256.ofNat ats.length :: attestationArrayHeads ats ats.length) ++
    attestationArrayBodies ats ats.length

theorem attestationArray_step (ats : List AttestationRecord) (i : Nat) (hi : i < ats.length) :
    attestationArrayBodies ats (i+1) = attestationArrayBodies ats i ++ ats[i].encoding ∧
    attestationArrayHeads ats (i+1) = attestationArrayHeads ats i ++ [UInt256.ofNat (attestationArrayOffset ats i)] ∧
    attestationArrayOffset ats (i+1) = attestationArrayOffset ats i + ats[i].encoding.size := by
  have ht : ats.take (i+1) = ats.take i ++ [ats[i]] := List.take_succ_eq_append_getElem hi
  simp only [attestationArrayBodies, attestationArrayHeads, attestationArrayOffset, ht,
    List.map_append, List.map_cons, List.map_nil, dynamicBodies_append, dynamicOffsets_append,
    dynamicBodies, dynamicOffsets, ByteArray.append_empty, ByteArray.size_append, Nat.add_assoc, and_self]

theorem attestationArrayOffset_le (ats : List AttestationRecord) (i : Nat) :
    attestationArrayOffset ats i ≤ attestationArrayOffset ats ats.length := by
  unfold attestationArrayOffset attestationArrayBodies
  rw [List.take_length, List.map_take]
  exact Nat.add_le_add_left (dynamicBodies_take_size_le _ _) _

end Benchmarks.EAS.EAS
