import Benchmarks.EAS.EAS.TimeEntry
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: list indexing agrees with mapping its elements.
theorem lookupNth_map {α β : Type} (f : α → β) (xs : List α) (i : Nat) :
    lookupNth? (xs.map f) i = (lookupNth? xs i).map f := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih => cases i with
    | zero => rfl
    | succ i => exact ih i

-- LIBRARY CANDIDATE: the semantic indexer is the standard optional list lookup.
theorem lookupNth_getElem {α : Type} (xs : List α) (i : Nat) : lookupNth? xs i = xs[i]? := by
  induction xs generalizing i with
  | nil => cases i <;> rfl
  | cons x xs ih => cases i with
    | zero => rfl
    | succ i => exact ih i

structure TimeArrayInv (locals : Store) (words : List UInt256) (time : UInt256) (heap i : Nat) : Prop where
  data : locals.get? "data" = some (.array (words.map wordBytes32Value))
  length : locals.get? "length" = some (.int (Int.ofNat words.length))
  time : locals.get? "time" = some (.int (Int.ofNat time.toNat))
  heap : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))
  index : locals.get? "i" = some (.int (Int.ofNat i))

def timeArrayGuard : Expr := .binary .lt (.var "i") (.var "length")

theorem timeArrayGuard_eval {cfg : Config} {evm : EVM.State} {locals imms : Store}
    {words : List UInt256} {time : UInt256} {heap i : Nat}
    (h : TimeArrayInv locals words time heap i) :
    evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm timeArrayGuard =
      .ok (.bool (decide (i < words.length))) := by
  simp only [timeArrayGuard, evalExpr?, h.index, h.length, EvalResult.ofOption, EvalResult.bind, bind,
    evalBinaryOp_lt_int_ok, Int.ofNat_eq_natCast, Nat.cast_lt]

theorem timeArrayArgs_eval {cfg : Config} {evm : EVM.State} {locals imms : Store}
    {words : List UInt256} {time : UInt256} {heap i : Nat} {word : UInt256}
    (h : TimeArrayInv locals words time heap i) (hi : i < words.length)
    (hw : lookupNth? words i = some word) :
    evalExprs? cfg {contract := contract, locals := locals, immutables := imms} evm
      [.index (.var "data") (.var "i"), .var "time", .var "$EAS.freeMemory"] =
      .ok [wordBytes32Value word, .int (Int.ofNat time.toNat), .int (Int.ofNat heap)] := by
  simp only [evalExprs?, evalExpr?, h.data, h.index, h.time, h.heap,
    EvalResult.ofOption, EvalResult.bind, bind, evalIndex?, Int.ofNat_eq_natCast,
    Int.natCast_nonneg, List.length_map, Nat.cast_lt, hi, and_self, if_true,
    Int.toNat_natCast, lookupNth_map, hw, Option.map_some, wordBytes32Value, normalizeRawBoolWord?, pure]

def timeArrayNext (locals : Store) (heap i : Nat) : Store :=
  (unpackHeapLocals (locals.insert "__c1$allocation" (.tuple [.tuple [], .int (Int.ofNat heap)]))
    "__c1" "$EAS.freeMemory" (.tuple []) heap).insert "i" (.int (Int.ofNat (i + 1)))

theorem timeArrayNext_inv {locals : Store} {words : List UInt256} {time : UInt256} {heap i : Nat}
    (h : TimeArrayInv locals words time heap i) :
    TimeArrayInv (timeArrayNext locals heap i) words time heap (i + 1) := by
  constructor
  · simpa [timeArrayNext, unpackHeapLocals, Std.HashMap.getElem?_insert] using h.data
  · simpa [timeArrayNext, unpackHeapLocals, Std.HashMap.getElem?_insert] using h.length
  · simpa [timeArrayNext, unpackHeapLocals, Std.HashMap.getElem?_insert] using h.time
  · simp only [timeArrayNext, store_get_ne _ _ (by decide : ("i" == "$EAS.freeMemory") = false),
      unpackHeapLocals, store_get_self]
  · exact store_get_self _ _ _

end Benchmarks.EAS.EAS
