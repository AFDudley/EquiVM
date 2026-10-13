import Benchmarks.EAS.EAS.TimeArray
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: the semantic list updater is standard replacement at an in-bounds index.
theorem updateNth_set {α : Type} (values : List α) (i : Nat) (value : α)
    (hi : i < values.length) : updateNth? values i value = some (values.set i value) := by
  induction values generalizing i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons v vs ih =>
    cases i with
    | zero => rfl
    | succ i => simp only [updateNth?,ih i (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi),
        bind,Option.bind,pure,List.set_cons_succ]

-- GENERALIZES the local-array assignment in EAS/Attester to arbitrary index expressions and nested paths.
theorem updateLocalArrayIndex {cfg : Config} {frame : Frame} {evm : EVM.State}
    {values : List Value} {index : Expr} {i : Nat} {value : Value}
    (he : evalExpr? cfg frame evm index = .ok (.int (Int.ofNat i))) (hi : i < values.length) :
    updateLocalPath? cfg frame evm (.array values) [.aindex index] value = .ok (.array (values.set i value)) := by
  simp only [updateLocalPath?,he,EvalResult.bind,bind,pure,
    Int.ofNat_eq_natCast,Int.toNat_natCast,show 0 ≤ (i : Int) by omega,
    show (i : Int) < values.length by omega,and_self,if_true,lookupIndex?,
    intToNat?,show ¬ (i : Int) < 0 by omega,if_false,lookupNth_getElem,List.getElem?_eq_getElem hi,
    updateIndex?,updateNth_set _ _ _ hi,EvalResult.ofOption,Option.bind]

theorem assignLocalArrayExpr {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {values : List Value} {index : Expr} {i : Nat} {value : Value}
    (ha : frame.locals.get? name = some (.array values))
    (he : evalExpr? cfg frame evm index = .ok (.int (Int.ofNat i))) (hi : i < values.length) :
    assignStorageRef? cfg frame evm .localVar {base := name,steps := [.aindex index]} value =
      .ok ({frame with locals := frame.locals.insert name (.array (values.set i value))},evm) := by
  simp only [assignStorageRef?,ha,updateLocalArrayIndex he hi,EvalResult.bind,bind,pure]

end Benchmarks.EAS.EAS
