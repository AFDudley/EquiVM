import Benchmarks.UniswapV3.Pool.Storage

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: Reasoning.SteleBody, a fixed or dynamic array field after a valid index.
theorem evalStorageRef_aindex_field_ok {cfg : Config} {frame : Frame} {evm : EVM.State}
    {base field : Ident} {index : Expr} {value : Value} {key : KeyValue}
    (heval : evalExpr? cfg frame evm index = .ok value)
    (hkey : valueToKey? value = some key)
    (hbound : arrayIndexInBounds? cfg evm frame.contract.storage base [] key = .ok ()) :
    evalStorageRef cfg frame evm ⟨base, [.aindex index, .field field]⟩ =
      .ok ⟨base, [.aindex key, .field field]⟩ := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, heval,
    hkey, hbound, EvalResult.bind, bind, pure, EvalResult.ofOption, List.nil_append]

-- LIBRARY CANDIDATE: Reasoning.SteleBody, an array field read stops at a failing bounds check.
theorem evalStorageRef_aindex_field_revert {cfg : Config} {frame : Frame} {evm : EVM.State}
    {base field : Ident} {index : Expr} {value : Value} {key : KeyValue}
    (heval : evalExpr? cfg frame evm index = .ok value)
    (hkey : valueToKey? value = some key)
    (hbound : arrayIndexInBounds? cfg evm frame.contract.storage base [] key = .revert) :
    evalStorageRef cfg frame evm ⟨base, [.aindex index, .field field]⟩ = .revert := by
  simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, heval,
    hkey, hbound, EvalResult.bind, bind, pure, EvalResult.ofOption]

-- LIBRARY CANDIDATE: Reasoning.SteleBody, propagate a reverting storage reference.
theorem evalExpr_storage_ref_revert {cfg : Config} {frame : Frame} {evm : EVM.State}
    {ref : StorageRef} (hbase : frame.locals.get? ref.base = none)
    (href : evalStorageRef cfg frame evm ref = .revert) :
    evalExpr? cfg frame evm (.storage ref) = .revert := by
  rw [evalExpr?]
  simp only [resolveStorageRef?, hbase, href, bind, EvalResult.bind]

end Benchmarks.UniswapV3.Pool
