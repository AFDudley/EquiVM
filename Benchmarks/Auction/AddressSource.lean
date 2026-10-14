import Reasoning.Storage
import Benchmarks.Auction.Storage

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem evalZeroAddr (cfg : Config) (stele : Frame) (evm : EVM.State) :
    evalExpr? cfg stele evm zeroAddr = .ok (.address (AccountAddress.ofNat 0)) := by
  simp [zeroAddr, addrSt, evalExpr?, EvalResult.bind, EvalResult.ofOption, castValue?, bind, pure]


theorem evalAddressNeZero_true {cfg : Config} {stele : Frame} {evm : EVM.State}
    {expr : Expr} {value : AccountAddress}
    (heval : evalExpr? cfg stele evm expr = .ok (.address value))
    (hz : value ≠ AccountAddress.ofNat 0) :
    evalExpr? cfg stele evm (.binary .ne expr zeroAddr) = .ok (.bool true) := by
  have hv : (Value.address value == Value.address (AccountAddress.ofNat 0)) = false := by
    rw [beq_eq_false_iff_ne]
    exact fun h => hz (Value.address.inj h)
  simp only [evalExpr?, heval, evalZeroAddr, EvalResult.bind, bind, evalBinaryOp?, hv,
    Bool.not_false]

theorem evalAddressNeZero_false {cfg : Config} {stele : Frame} {evm : EVM.State}
    {expr : Expr} {value : AccountAddress}
    (heval : evalExpr? cfg stele evm expr = .ok (.address value))
    (hz : value = AccountAddress.ofNat 0) :
    evalExpr? cfg stele evm (.binary .ne expr zeroAddr) = .ok (.bool false) := by
  have hv : (Value.address value == Value.address (AccountAddress.ofNat 0)) = true := by
    rw [hz]
    exact beq_self_eq_true _
  simp only [evalExpr?, heval, evalZeroAddr, EvalResult.bind, bind, evalBinaryOp?, hv,
    Bool.not_true]

end Auction
