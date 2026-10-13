import Benchmarks.CurveVault.Common
import Reasoning.SolmArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: Vyper detects checked subtraction underflow with GT.
theorem u256_sub_underflow_gt (a b : UInt256) (h : a.toNat < b.toNat) :
    UInt256.gt (UInt256.sub a b) a = ⟨1⟩ := by
  apply ugt_one
  rw [usub_toNat_underflow h]
  have hb : b.toNat < UInt256.size := b.val.isLt
  omega

-- LIBRARY CANDIDATE: a uint256 cast after addition agrees with wrapping word addition.
theorem evalExpr_castAdd256 {cfg : Config} {solm : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat b.toNat))) :
    evalExpr? cfg solm evm (.cast (.binary .add lhs rhs) (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat (a + b).toNat)) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?, castValue?,
    normalizeInt, EvalResult.ofOption, uadd_toNat]
  congr 2

-- LIBRARY CANDIDATE: a uint256 cast after subtraction agrees with wrapping subtraction.
theorem evalExpr_castSub256 {cfg : Config} {solm : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat b.toNat))) :
    evalExpr? cfg solm evm (.cast (.binary .sub lhs rhs) (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat (UInt256.sub a b).toNat)) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?, castValue?,
    normalizeInt, EvalResult.ofOption]
  congr 2
  have haBound := a.val.isLt
  have hbBound := b.val.isLt
  change a.toNat < UInt256.size at haBound
  change b.toNat < UInt256.size at hbBound
  by_cases hle : b.toNat ≤ a.toNat
  · rw [usub_toNat hle]
    change (Int.ofNat a.toNat - Int.ofNat b.toNat) % (2 ^ 256) = Int.ofNat (a.toNat - b.toNat)
    change a.toNat < 2 ^ 256 at haBound
    simp only [Int.ofNat_eq_natCast]
    omega
  · rw [usub_toNat_underflow (by omega)]
    change (Int.ofNat a.toNat - Int.ofNat b.toNat) % (2 ^ 256) = Int.ofNat (2 ^ 256 + a.toNat - b.toNat)
    change b.toNat < 2 ^ 256 at hbBound
    simp only [Int.ofNat_eq_natCast]
    omega

-- LIBRARY CANDIDATE: Vyper recognizes the all-ones sentinel with NOT.
theorem u256_lnot_eq_zero_iff (w : UInt256) :
    UInt256.lnot w = ⟨0⟩ ↔ w = UInt256.ofNat (UInt256.size - 1) := by
  have hm : (UInt256.ofNat (UInt256.size - 1)).toNat = UInt256.size - 1 :=
    ulit_toNat' _ (by decide +kernel)
  constructor
  · intro h
    apply u256_inj
    have hn := congrArg UInt256.toNat h
    rw [lnot_toNat_gen] at hn
    change UInt256.size - 1 - w.toNat = 0 at hn
    have hw : w.toNat < UInt256.size := w.val.isLt
    rw [hm]
    omega
  · rintro rfl
    decide +kernel

-- LIBRARY CANDIDATE: checked binary arithmetic propagates a left operand's revert.
theorem evalExpr_checked_binary_left_revert {cfg : Config} {solm : Frame} {evm : State}
    {lhs rhs : Expr} (op : BinaryOp) (ty : IntType)
    (h : evalExpr? cfg solm evm lhs = .revert) :
    evalExpr? cfg solm evm (.inRange ty (.binary op lhs rhs)) = .revert := by
  cases op <;> simp [evalExpr?, h, bind, EvalResult.bind]


-- LIBRARY CANDIDATE: checked multiplication propagates a right operand's
-- revert after the left operand evaluates successfully.
theorem evalExpr_checked_mul_right_revert {cfg : Config} {solm : Frame} {evm : State}
    {lhs rhs : Expr} {v : Value} (ty : IntType)
    (hl : evalExpr? cfg solm evm lhs = .ok v) (hr : evalExpr? cfg solm evm rhs = .revert) :
    evalExpr? cfg solm evm (.inRange ty (.binary .mul lhs rhs)) = .revert := by
  simp [evalExpr?, hl, hr, bind, EvalResult.bind]
end Benchmarks.CurveVault
