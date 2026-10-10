import Benchmarks.EAS.EAS.Allocate
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: a natural-valued word compares equal to zero exactly when its EVM word does.
theorem evalWordEqZero {cfg : Config} {frame : Frame} {evm : EVM.State} {expr : Expr} {word : UInt256}
    (he : evalExpr? cfg frame evm expr = .ok (.int (Int.ofNat word.toNat))) :
    evalExpr? cfg frame evm (.binary .eq expr (.intLit 0)) = .ok (.bool (decide (word = ⟨0⟩))) := by
  simp only [evalExpr?, he, EvalResult.bind, bind, pure, evalBinaryOp?]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.int.injEq, Int.ofNat_eq_natCast, Int.natCast_eq_zero, decide_eq_true_eq]
  exact ⟨uint256_toNat_eq_zero, fun h => by rw [h]; rfl⟩

-- GENERALIZES Reasoning.SolmArithmetic.evalExpr_ne_int_true/false to arbitrary frames and word values.
theorem evalWordNeZero {cfg : Config} {frame : Frame} {evm : EVM.State} {expr : Expr} {word : UInt256}
    (he : evalExpr? cfg frame evm expr = .ok (.int (Int.ofNat word.toNat))) :
    evalExpr? cfg frame evm (.binary .ne expr (.intLit 0)) = .ok (.bool (decide (word ≠ ⟨0⟩))) := by
  have h := evalWordEqZero he
  simp only [evalExpr?, he, EvalResult.bind, bind, pure, evalBinaryOp?] at h ⊢
  have hb := Value.bool.inj (EvalResult.ok.inj h)
  rw [hb]
  simp only [ne_eq, decide_not]

-- GENERALIZES Reasoning.SolmBody.evalExpr_uint256_sub to the uint256 cast form.
theorem evalCastUint256Sub {cfg : Config} {frame : Frame} {evm : EVM.State}
    {a b : Expr} {x y : UInt256}
    (hx : evalExpr? cfg frame evm a = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg frame evm b = .ok (.int (Int.ofNat y.toNat))) (hle : y.toNat ≤ x.toNat) :
    evalExpr? cfg frame evm (.cast (.binary .sub a b) (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat (UInt256.sub x y).toNat)) := by
  have hb : x.toNat-y.toNat < 2^256 := by have h := x.val.isLt; change x.toNat < 2^256 at h; omega
  simp only [evalExpr?, hx, hy, EvalResult.bind, bind, evalBinaryOp?, castValue?,
    normalizeInt, EvalResult.ofOption, usub_toNat hle, Int.ofNat_eq_natCast, ← Int.ofNat_sub hle]
  have he : ((x.toNat-y.toNat : Nat) : Int) % (2^256) = ((x.toNat-y.toNat : Nat) : Int) := by
    apply Int.emod_eq_of_lt (by omega)
    exact_mod_cast hb
  change EvalResult.ok (Value.int (((x.toNat-y.toNat : Nat) : Int) % (2^256))) = _
  rw [he]

end Benchmarks.EAS.EAS
