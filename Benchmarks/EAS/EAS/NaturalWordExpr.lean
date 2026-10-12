import Benchmarks.EAS.EAS.Allocate
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: multiplication of natural-valued expressions.
theorem naturalMulSource {cfg : Config} {frame : Frame} {evm : EVM.State} {a b : Expr} {x y : Nat}
    (ha : evalExpr? cfg frame evm a=.ok (.int (Int.ofNat x)))
    (hb : evalExpr? cfg frame evm b=.ok (.int (Int.ofNat y))) :
    evalExpr? cfg frame evm (.binary .mul a b)=.ok (.int (Int.ofNat (x*y))) := by
  simp only [evalExpr?,ha,hb,bind,EvalResult.bind,evalBinaryOp?,Int.ofNat_eq_natCast,Nat.cast_mul]

-- LIBRARY CANDIDATE: a uint256 cast reduces a natural value modulo the word size.
theorem evalCastUint256Nat {cfg : Config} {frame : Frame} {evm : EVM.State} {e : Expr} {n : Nat}
    (he : evalExpr? cfg frame evm e=.ok (.int (Int.ofNat n))) :
    evalExpr? cfg frame evm (.cast e (.elem (.int (.uint ⟨256,by decide⟩))))=.ok (.int (Int.ofNat (UInt256.ofNat n).toNat)) := by
  simp only [evalExpr?,he,bind,EvalResult.bind,castValue?,normalizeInt,EvalResult.ofOption,Int.ofNat_eq_natCast]
  change EvalResult.ok (Value.int ((n:Int)%2^256))=EvalResult.ok (Value.int ((n%2^256:Nat):Int))
  norm_cast

-- LIBRARY CANDIDATE: a cast sum agrees with addition of EVM words.
theorem evalCastWordAdd {cfg : Config} {frame : Frame} {evm : EVM.State} {a b : Expr} {x y : UInt256}
    (ha : evalExpr? cfg frame evm a=.ok (.int (Int.ofNat x.toNat)))
    (hb : evalExpr? cfg frame evm b=.ok (.int (Int.ofNat y.toNat))) :
    evalExpr? cfg frame evm (.cast (.binary .add a b) (.elem (.int (.uint ⟨256,by decide⟩))))=.ok (.int (Int.ofNat (x+y).toNat)) := by
  have h := evalCastUint256Add ha hb
  simpa only [uadd_toNat] using h

end Benchmarks.EAS.EAS
