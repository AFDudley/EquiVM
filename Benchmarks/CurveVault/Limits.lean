import Benchmarks.CurveVault.Arithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def wordMax (a b : UInt256) : UInt256 := if b.toNat < a.toNat then a else b

def wordMin (a b : UInt256) : UInt256 := if a.toNat < b.toNat then a else b

-- LIBRARY CANDIDATE: an unsigned minimum expressed as a conditional.
theorem evalExpr_min256 {cfg : Config} {solm : Frame} {evm : State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat b.toNat))) :
    evalExpr? cfg solm evm (.ite (.binary .lt lhs rhs) lhs rhs) =
      .ok (.int (Int.ofNat (wordMin a b).toNat)) := by
  by_cases hlt : a.toNat < b.toNat
  · rw [wordMin, if_pos hlt]
    simp [evalExpr?, ha, hb, evalBinaryOp?, bind, EvalResult.bind, hlt]
  · rw [wordMin, if_neg hlt]
    simp [evalExpr?, ha, hb, evalBinaryOp?, bind, EvalResult.bind, hlt]

-- GENERALIZES Reasoning.VyperDispatch.branchlessMin to the GT-based maximum.
theorem branchlessMax (a b : UInt256) :
    UInt256.xor (UInt256.mul (UInt256.gt a b) (UInt256.xor b a)) b = wordMax a b := by
  unfold wordMax
  split
  · rename_i h
    rw [ugt_one h, u256_one_mul, u256_xor_xor_cancel]
  · rename_i h
    rw [ugt_zero (by omega), u256_mul_zero_left, u256_zero_xor]

theorem wordMax_ge_right (a b : UInt256) : b.toNat ≤ (wordMax a b).toNat := by
  unfold wordMax
  split <;> omega

theorem sub_wordMax_noUnderflow (a b : UInt256) :
    UInt256.gt (UInt256.sub (wordMax a b) b) (wordMax a b) = ⟨0⟩ :=
  ugt_zero (by rw [usub_toNat (wordMax_ge_right a b)]; omega)

-- LIBRARY CANDIDATE: an unsigned maximum expressed as a conditional.
theorem evalExpr_max256 {cfg : Config} {solm : Frame} {evm : State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat b.toNat))) :
    evalExpr? cfg solm evm (.ite (.binary .gt lhs rhs) lhs rhs) =
      .ok (.int (Int.ofNat (wordMax a b).toNat)) := by
  by_cases hgt : b.toNat < a.toNat
  · rw [wordMax, if_pos hgt]
    simp [evalExpr?, ha, hb, evalBinaryOp?, bind, EvalResult.bind, hgt]
  · rw [wordMax, if_neg hgt]
    simp [evalExpr?, ha, hb, evalBinaryOp?, bind, EvalResult.bind, hgt]

-- LIBRARY CANDIDATE: checked max(a,b)-b implements subtraction clamped at zero.
theorem evalExpr_checkedMaxSub256 {cfg : Config} {solm : Frame} {evm : State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat b.toNat))) :
    evalExpr? cfg solm evm (.inRange (.uint ⟨256, by decide⟩)
      (.binary .sub (.ite (.binary .gt lhs rhs) lhs rhs) rhs)) =
      .ok (.int (Int.ofNat (UInt256.sub (wordMax a b) b).toNat)) :=
  evalExpr_uint256_sub (evalExpr_max256 ha hb) hb (wordMax_ge_right a b)

-- LIBRARY CANDIDATE: casting a nonnegative uint256 difference preserves its word.
theorem evalExpr_castSub256_of_le {cfg : Config} {solm : Frame} {evm : State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat b.toNat)))
    (hle : b.toNat ≤ a.toNat) :
    evalExpr? cfg solm evm (.cast (.binary .sub lhs rhs) (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat (UInt256.sub a b).toNat)) := by
  have hd : Int.ofNat a.toNat - Int.ofNat b.toNat = Int.ofNat (UInt256.sub a b).toNat := by
    rw [usub_toNat hle]
    exact (Int.ofNat_sub hle).symm
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?, hd, castValue?,
    normalizeInt_uint256_word, EvalResult.ofOption, pure]
end Benchmarks.CurveVault
