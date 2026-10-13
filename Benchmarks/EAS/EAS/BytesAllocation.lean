import Benchmarks.EAS.EAS.AllocateBlock
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: the word-aligned allocation size of a byte-array payload.
def bytesAllocation (size : Nat) : Nat := 32 + (size + 31) / 32 * 32

def bytesAllocationExpr (length : Expr) : Expr := .binary .add (.intLit 32)
  (.binary .mul (.binary .div (.binary .add length (.intLit 31)) (.intLit 32)) (.intLit 32))

-- LIBRARY CANDIDATE: evaluating the standard byte-array allocation formula.
theorem bytesAllocationExpr_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {length : Expr} {size : Nat}
    (hl : evalExpr? cfg frame evm length = .ok (.int (Int.ofNat size))) :
    evalExpr? cfg frame evm (bytesAllocationExpr length) = .ok (.int (Int.ofNat (bytesAllocation size))) := by
  have he : evalExpr? cfg frame evm (.binary .add length (.intLit 31)) = .ok (.int (Int.ofNat (size+31))) := by
    simp only [evalExpr?, hl, EvalResult.bind, bind, pure, evalBinaryOp?]
    simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_ofNat]
  have hf := evalFloor32 he
  simp only [bytesAllocationExpr, evalExpr?, hf, pure, bind, EvalResult.bind, evalBinaryOp?]
  simp only [bytesAllocation, Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_ofNat]

end Benchmarks.EAS.EAS
