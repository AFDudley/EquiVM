import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateArithmeticSource

/-! The source cap read and checked supply-cap guard. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
attribute [local irreducible] contract

def reallocateSupplyCapFrame (frame : Frame) (cap : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "supplyCap" (uint256Value cap) }

theorem reallocateSupplyCapSource {frame : Frame} {evm : State} {assets amount id : UInt256}
    (hc : frame.contract = contract) (hcfg : frame.locals.get? "config" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (ha : frame.locals.get? "supplyAssets" = some (uint256Value assets))
    (hm : frame.locals.get? "suppliedAssets" = some (uint256Value amount))
    (hcap : assets.toNat + amount.toNat ≤ (marketRemovalCap evm id).toNat) :
    ExecBlock config frame evm ((reallocateSupplyBody.drop 4).take 2)
      (.ok (reallocateSupplyCapFrame frame (marketRemovalCap evm id)) evm) := by
  apply ExecBlock.consNormal (ExecStmt.letDecl (maxDepositCapRead hc hcfg hid))
  let frame1 := reallocateSupplyCapFrame frame (marketRemovalCap evm id)
  have ha1 : frame1.locals.get? "supplyAssets" = some (uint256Value assets) := by
    dsimp only [frame1, reallocateSupplyCapFrame]
    rw [store_get_ne _ _ (by decide)]; exact ha
  have hm1 : frame1.locals.get? "suppliedAssets" = some (uint256Value amount) := by
    dsimp only [frame1, reallocateSupplyCapFrame]
    rw [store_get_ne _ _ (by decide)]; exact hm
  have hc1 : frame1.locals.get? "supplyCap" = some (uint256Value (marketRemovalCap evm id)) :=
    store_get_self _ _ _
  have hfit : assets.toNat + amount.toNat < UInt256.size :=
    lt_of_le_of_lt hcap (marketRemovalCap evm id).val.isLt
  have htest := naturalLeSource (cfg := config) (evm := evm)
    (checkedAddSourceOk (evalLocalValue ha1) (evalLocalValue hm1) hfit) (evalLocalValue hc1)
  have hsum : (assets + amount).toNat = assets.toNat + amount.toNat := addWord_toNat _ _ hfit
  rw [hsum, decide_eq_true hcap] at htest
  exact ExecBlock.consNormal (ExecStmt.requireTrue htest) ExecBlock.nil

theorem reallocateSupplyCapRevert {frame : Frame} {evm : State} {assets amount id : UInt256}
    (hc : frame.contract = contract) (hcfg : frame.locals.get? "config" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (ha : frame.locals.get? "supplyAssets" = some (uint256Value assets))
    (hm : frame.locals.get? "suppliedAssets" = some (uint256Value amount))
    (hcap : (marketRemovalCap evm id).toNat < assets.toNat + amount.toNat) :
    ExecBlock config frame evm (reallocateSupplyBody.drop 4) .reverted := by
  apply ExecBlock.consNormal (ExecStmt.letDecl (maxDepositCapRead hc hcfg hid))
  let frame1 := reallocateSupplyCapFrame frame (marketRemovalCap evm id)
  have ha1 : frame1.locals.get? "supplyAssets" = some (uint256Value assets) := by
    dsimp only [frame1, reallocateSupplyCapFrame]
    rw [store_get_ne _ _ (by decide)]; exact ha
  have hm1 : frame1.locals.get? "suppliedAssets" = some (uint256Value amount) := by
    dsimp only [frame1, reallocateSupplyCapFrame]
    rw [store_get_ne _ _ (by decide)]; exact hm
  have hc1 : frame1.locals.get? "supplyCap" = some (uint256Value (marketRemovalCap evm id)) :=
    store_get_self _ _ _
  by_cases hfit : assets.toNat + amount.toNat < UInt256.size
  · have htest := naturalLeSource (cfg := config) (evm := evm)
      (checkedAddSourceOk (evalLocalValue ha1) (evalLocalValue hm1) hfit) (evalLocalValue hc1)
    have hsum : (assets + amount).toNat = assets.toNat + amount.toNat := addWord_toNat _ _ hfit
    rw [hsum, decide_eq_false (Nat.not_le_of_gt hcap)] at htest
    exact ExecBlock.consRevert (ExecStmt.requireFalse htest)
  · have hsum := checkedAddSourceOverflow (cfg := config) (evm := evm) (evalLocalValue ha1) (evalLocalValue hm1)
      (Nat.le_of_not_gt hfit)
    apply ExecBlock.consRevert (ExecStmt.requireRevert (stele := frame1) ?_)
    rw [evalExpr_binary_nonshort (by decide) (by decide), hsum]
    rfl

theorem ReallocateLocals.supplyCap {v : MetaMorphoV1_1Immutables} {frame : Frame} {values : List Value}
    {i supplied withdrawn cursor : UInt256} (h : ReallocateLocals v frame values i supplied withdrawn cursor)
    (cap : UInt256) :
    ReallocateLocals v (reallocateSupplyCapFrame frame cap) values i supplied withdrawn cursor :=
  h.insert "supplyCap" _ (by decide)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
