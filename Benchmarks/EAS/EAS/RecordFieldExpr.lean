import Benchmarks.EAS.EAS.WordExpr
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- GENERALIZES attestationRecord_field to arbitrary record-valued expressions and field names.
theorem evalRecordField {cfg : Config} {frame : Frame} {evm : EVM.State} {expr : Expr}
    {record value : Value} {field : Ident}
    (he : evalExpr? cfg frame evm expr = .ok record) (hf : lookupField? record field = some value) :
    evalExpr? cfg frame evm (.field expr field) = .ok value := by
  cases record <;> try { simp [lookupField?] at hf }
  simp only [evalExpr?,he,EvalResult.bind,bind]
  change EvalResult.ofOption .typeError _ = _
  simpa only [lookupField?,EvalResult.ofOption] using congrArg (EvalResult.ofOption (α := Value) .typeError) hf

end Benchmarks.EAS.EAS
