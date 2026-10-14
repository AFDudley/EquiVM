import Benchmarks.EAS.EAS.ArrayLoopSource
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- GENERALIZES evalLocalNewArray to an arbitrary evaluated length expression.
theorem evalNewArrayExpr {cfg : Config} {frame : Frame} {evm : EVM.State}
    {length : Expr} {ty : StorageType} {value : Value} {n : Nat}
    (hn : evalExpr? cfg frame evm length = .ok (.int (Int.ofNat n)))
    (hd : defaultValue? ty = .ok value) :
    evalExpr? cfg frame evm (.newArray ty length) = .ok (.array (List.replicate n value)) := by
  rw [evalExpr?,hn]
  simp only [bind,EvalResult.bind,Int.ofNat_eq_natCast,show ¬ (n : Int) < 0 by omega,if_false,hd,pure,Int.toNat_natCast]

end Benchmarks.EAS.EAS
