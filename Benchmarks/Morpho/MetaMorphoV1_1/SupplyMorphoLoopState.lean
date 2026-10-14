import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoReadersSource
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoArithmeticSource
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoCallSource

/-! Source-local invariants for the supply loop, including both outcomes of a caught call. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

attribute [local irreducible] contract

structure SupplyLoopLocals (v : MetaMorphoV1_1Immutables) (frame : Frame)
    (i assets cursor : UInt256) : Prop where
  contract : frame.contract = Benchmarks.Morpho.MetaMorphoV1_1.contract
  imms : frame.immutables = immStore v
  target : frame.locals.get? "morphoTarget" = some (.address v.MORPHO)
  index : frame.locals.get? "i" = some (uint256Value i)
  assets : frame.locals.get? "assets" = some (uint256Value assets)
  cursor : frame.locals.get? cursorName = some (uint256Value cursor)
  queue : frame.locals.get? "supplyQueue" = none
  config : frame.locals.get? "config" = none

theorem SupplyLoopLocals.insert {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i assets cursor : UInt256} (h : SupplyLoopLocals v frame i assets cursor)
    (name : Ident) (value : Value)
    (hm : (name == "morphoTarget") = false) (hi : (name == "i") = false)
    (ha : (name == "assets") = false) (hc : (name == cursorName) = false)
    (hq : (name == "supplyQueue") = false) (hg : (name == "config") = false) :
    SupplyLoopLocals v { frame with locals := frame.locals.insert name value } i assets cursor := by
  refine ⟨h.contract, h.imms, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [store_get_ne _ _ hm]; exact h.target
  · rw [store_get_ne _ _ hi]; exact h.index
  · rw [store_get_ne _ _ ha]; exact h.assets
  · rw [store_get_ne _ _ hc]; exact h.cursor
  · rw [store_get_ne _ _ hq]; exact h.queue
  · rw [store_get_ne _ _ hg]; exact h.config

theorem SupplyLoopLocals.withCursor {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i assets cursor : UInt256} (h : SupplyLoopLocals v frame i assets cursor) (ptr : UInt256) :
    SupplyLoopLocals v { frame with locals := frame.locals.insert cursorName (uint256Value ptr) }
      i assets ptr := by
  refine ⟨h.contract, h.imms, ?_, ?_, ?_, store_get_self _ _ _, ?_, ?_⟩ <;>
    rw [store_get_ne _ _ (by decide)]
  · exact h.target
  · exact h.index
  · exact h.assets
  · exact h.queue
  · exact h.config

theorem SupplyLoopLocals.withAssets {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i assets cursor : UInt256} (h : SupplyLoopLocals v frame i assets cursor) (amount : UInt256) :
    SupplyLoopLocals v { frame with locals := frame.locals.insert "assets" (uint256Value amount) }
      i amount cursor := by
  refine ⟨h.contract, h.imms, ?_, ?_, store_get_self _ _ _, ?_, ?_, ?_⟩ <;>
    rw [store_get_ne _ _ (by decide)]
  · exact h.target
  · exact h.index
  · exact h.cursor
  · exact h.queue
  · exact h.config

theorem SupplyLoopLocals.post {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i assets cursor : UInt256} (h : SupplyLoopLocals v frame i assets cursor) :
    SupplyLoopLocals v (maxDepositPostFrame frame i) (i + ⟨1⟩) assets cursor := by
  refine ⟨h.contract, h.imms, ?_, store_get_self _ _ _, ?_, ?_, ?_, ?_⟩ <;>
    rw [maxDepositPostFrame, store_get_ne _ _ (by decide)]
  · exact h.target
  · exact h.assets
  · exact h.cursor
  · exact h.queue
  · exact h.config

theorem SupplyLoopLocals.cap {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i assets cursor : UInt256} (h : SupplyLoopLocals v frame i assets cursor) (id cap : UInt256) :
    SupplyLoopLocals v (maxDepositCapFrame frame id cap) i assets cursor := by
  have h1 := h.insert "id" (wordBytes32Value id)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact h1.insert "supplyCap" (uint256Value cap)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem SupplyLoopLocals.readers {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i assets cursor : UInt256} (h : SupplyLoopLocals v frame i assets cursor)
    (params : ByteArray) (ptr1 : UInt256) (market : ByteArray) (shares ptr2 : UInt256) :
    SupplyLoopLocals v (supplyMorphoReadersFrame frame params ptr1 market shares ptr2)
      i assets ptr2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, supplyMorphoReadersFrame_cursor frame params ptr1 market shares ptr2, ?_, ?_⟩
  · simpa only [supplyMorphoReadersFrame, cursorResultFrame, supplyMorphoMarketFrame,
      supplyMarketReservedFrame, supplyMarketFrame, supplyAccruedFrame, supplyMorphoParamsFrame]
      using h.contract
  · simpa only [supplyMorphoReadersFrame, cursorResultFrame, supplyMorphoMarketFrame,
      supplyMarketReservedFrame, supplyMarketFrame, supplyAccruedFrame, supplyMorphoParamsFrame]
      using h.imms
  all_goals rw [supplyMorphoReadersFrame_preserves _ _ _ _ _ _ _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  · exact h.target
  · exact h.index
  · exact h.assets
  · exact h.queue
  · exact h.config

theorem SupplyLoopLocals.arithmetic {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i assets cursor : UInt256} (h : SupplyLoopLocals v frame i assets cursor)
    (shares sa ss cap : UInt256) :
    SupplyLoopLocals v (supplyMorphoArithmeticFrame frame shares sa ss cap assets) i assets cursor := by
  refine ⟨h.contract, h.imms, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals rw [supplyMorphoArithmeticFrame_preserves _ _ _ _ _ _ _ (by decide) (by decide) (by decide)]
  · exact h.target
  · exact h.index
  · exact h.assets
  · exact h.cursor
  · exact h.queue
  · exact h.config

theorem SupplyLoopLocals.callFailure {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i assets cursor : UInt256} (h : SupplyLoopLocals v frame i assets cursor) (out : ByteArray) :
    SupplyLoopLocals v (supplyCallFailureFrame frame out) i assets cursor :=
  h.insert "__err" (.bytes out)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem SupplyLoopLocals.callSuccess {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i assets cursor : UInt256} (h : SupplyLoopLocals v frame i assets cursor)
    (amount : UInt256) (out : ByteArray) :
    SupplyLoopLocals v (supplyCallSuccessFrame frame cursor assets amount out)
      i (UInt256.sub assets amount) (nextCursor cursor ⟨64⟩) := by
  have h1 := h.insert "__ret" (.tuple [uint256Value (calldataWord out 0), uint256Value (calldataWord out 32)])
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact (h1.withCursor (nextCursor cursor ⟨64⟩)).withAssets (UInt256.sub assets amount)

theorem supplyMorphoDoneCondition {frame : Frame} {evm : State} {assets : UInt256}
    (ha : frame.locals.get? "assets" = some (uint256Value assets)) :
    evalExpr? config frame evm (.binary .eq (.var "assets") (.intLit 0)) =
      .ok (.bool (decide (assets = ⟨0⟩))) := by
  simp only [evalExpr?, ha, EvalResult.ofOption, uint256Value,
    bind, EvalResult.bind, evalBinaryOp?, pure, BEq.beq, Value.int.injEq]
  congr 3
  exact propext (by
    constructor
    · intro h; apply u256_inj; simpa using h
    · rintro rfl; rfl)

theorem supplyMorphoReturnSource {frame : Frame} {evm : State} {cursor : UInt256}
    (hc : frame.locals.get? cursorName = some (uint256Value cursor)) :
    ExecStmt config frame evm (.return [.tupleLit [], .var cursorName])
      (.returned frame evm (some [.tuple [], uint256Value cursor])) := by
  apply ExecStmt.return
  simp only [evalExprs?, evalExpr?, evalExprList?, hc, EvalResult.ofOption, bind, EvalResult.bind, pure]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
