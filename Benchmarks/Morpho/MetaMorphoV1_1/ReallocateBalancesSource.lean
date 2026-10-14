import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateLocals
import Benchmarks.Morpho.MetaMorphoV1_1.AccruedSupplyTailSource

/-! Project the accrued asset and share balances returned for a reallocation row. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def reallocateBalancesFrame (frame : Frame) (market : ByteArray) (shares : UInt256) : Frame :=
  { frame with locals := ((frame.locals.insert "supplyAssets" (uint256Value
      (assetsDownWord shares (calldataWord market 0) (calldataWord market 32)))).insert
        "supplyShares" (uint256Value shares)) }

theorem reallocateBalancesSource {frame : Frame} {evm : State} {market : ByteArray} {shares : UInt256}
    (h : frame.locals.get? "__c3" = some (accruedSupplyValue market shares)) :
    ExecBlock config frame evm reallocateRowBalances
      (.ok (reallocateBalancesFrame frame market shares) evm) := by
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value
    (assetsDownWord shares (calldataWord market 0) (calldataWord market 32))) ?_) ?_
  · simp only [evalExpr?, h, EvalResult.ofOption, accruedSupplyValue, tupleGetValue?,
      bind, EvalResult.bind, List.getElem?_cons_zero]
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := uint256Value shares) ?_) ExecBlock.nil
  simp only [evalExpr?, store_get_ne _ _ (by decide : ("supplyAssets" == "__c3") = false),
    h, EvalResult.ofOption, accruedSupplyValue, tupleGetValue?, bind, EvalResult.bind,
    List.getElem?_cons_succ, List.getElem?_cons_zero]

theorem reallocateBalancesFrame_preserves (frame : Frame) (market : ByteArray) (shares : UInt256)
    (name : Ident) (ha : ("supplyAssets" == name) = false) (hs : ("supplyShares" == name) = false) :
    (reallocateBalancesFrame frame market shares).locals.get? name = frame.locals.get? name := by
  rw [reallocateBalancesFrame, store_get_ne _ _ hs, store_get_ne _ _ ha]

theorem reallocateBalancesFrame_assets (frame : Frame) (market : ByteArray) (shares : UInt256) :
    (reallocateBalancesFrame frame market shares).locals.get? "supplyAssets" = some (uint256Value
      (assetsDownWord shares (calldataWord market 0) (calldataWord market 32))) := by
  rw [reallocateBalancesFrame, store_get_ne _ _ (by decide), store_get_self]

theorem reallocateBalancesFrame_shares (frame : Frame) (market : ByteArray) (shares : UInt256) :
    (reallocateBalancesFrame frame market shares).locals.get? "supplyShares" = some (uint256Value shares) :=
  store_get_self _ _ _

theorem ReallocateLocals.balances {v : MetaMorphoV1_1Immutables} {frame : Frame} {values : List Value}
    {i supplied withdrawn cursor : UInt256} (h : ReallocateLocals v frame values i supplied withdrawn cursor)
    (market : ByteArray) (shares : UInt256) :
    ReallocateLocals v (reallocateBalancesFrame frame market shares) values i supplied withdrawn cursor :=
  (h.insert "supplyAssets" (uint256Value
    (assetsDownWord shares (calldataWord market 0) (calldataWord market 32))) (by decide)).insert
      "supplyShares" (uint256Value shares) (by decide)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
