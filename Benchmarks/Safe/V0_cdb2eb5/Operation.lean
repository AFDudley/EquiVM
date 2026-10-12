import Benchmarks.Safe.V0_cdb2eb5.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V0_cdb2eb5

theorem evalValidOperation {cfg : Config} {frame : Frame} {evm : EVM.State} {op : UInt256}
    (hl : frame.locals["operation"]? = some (.int (Int.ofNat op.toNat))) :
    evalExpr? cfg frame evm validOperation = .ok (.bool (decide (op.toNat < 2))) := by
  simp [validOperation, leE, evalExpr?, hl, EvalResult.ofOption,
    EvalResult.bind, bind, pure, evalBinaryOp?]

end Benchmarks.Safe.V0_cdb2eb5
