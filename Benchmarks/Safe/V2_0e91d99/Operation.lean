import Benchmarks.Safe.V2_0e91d99.Common

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V2_0e91d99

theorem evalValidOperation {cfg : Config} {frame : Frame} {evm : EVM.State} {op : UInt256}
    (hl : frame.locals["operation"]? = some (.int (Int.ofNat op.toNat))) :
    evalExpr? cfg frame evm validOperation = .ok (.bool (decide (op.toNat < 2))) := by
  simp [validOperation, leE, evalExpr?, hl, EvalResult.ofOption,
    EvalResult.bind, bind, pure, evalBinaryOp?]

end Benchmarks.Safe.V2_0e91d99
