import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawMorphoCallSource
import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawLoopState
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoLoopState

/-! Invariants preserved by the mutating withdrawal loop's locals and caught calls. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

attribute [local irreducible] contract

structure WithdrawMorphoLocals (v : MetaMorphoV1_1Immutables) (frame : Frame)
    (i assets cursor : UInt256) extends WithdrawLoopLocals v frame i assets cursor : Prop where
  target : frame.locals.get? "morphoTarget" = some (.address v.MORPHO)

theorem WithdrawMorphoLocals.insert {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i assets cursor : UInt256} (h : WithdrawMorphoLocals v frame i assets cursor)
    (name : Ident) (value : Value) (hm : (name == "morphoTarget") = false)
    (hi : (name == "i") = false) (ha : (name == "assets") = false)
    (hc : (name == cursorName) = false) (hq : (name == "withdrawQueue") = false) :
    WithdrawMorphoLocals v { frame with locals := frame.locals.insert name value }
      i assets cursor :=
  ⟨h.toWithdrawLoopLocals.insert name value hi ha hc hq, by rw [store_get_ne _ _ hm]; exact h.target⟩

theorem WithdrawMorphoLocals.reader {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i assets cursor : UInt256} (h : WithdrawMorphoLocals v frame i assets cursor)
    (name : Ident) (value : Value) (ptr : UInt256) (hm : (name == "morphoTarget") = false)
    (hi : (name == "i") = false) (ha : (name == "assets") = false)
    (hq : (name == "withdrawQueue") = false) :
    WithdrawMorphoLocals v (cursorResultFrame frame name value ptr) i assets ptr :=
  ⟨h.toWithdrawLoopLocals.reader name value ptr hi ha hq, by
    rw [cursorResultFrame_preserves _ _ _ _ _ (by decide) hm (by decide)]; exact h.target⟩

theorem WithdrawMorphoLocals.withCursor {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i assets cursor : UInt256} (h : WithdrawMorphoLocals v frame i assets cursor) (ptr : UInt256) :
    WithdrawMorphoLocals v { frame with locals := frame.locals.insert cursorName (uint256Value ptr) }
      i assets ptr := by
  refine ⟨⟨h.contract, h.imms, ?_, ?_, store_get_self _ _ _, ?_⟩, ?_⟩ <;>
    rw [store_get_ne _ _ (by decide)]
  · exact h.index
  · exact h.assets
  · exact h.queue
  · exact h.target

theorem WithdrawMorphoLocals.withAssets {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i assets cursor : UInt256} (h : WithdrawMorphoLocals v frame i assets cursor) (amount : UInt256) :
    WithdrawMorphoLocals v { frame with locals := frame.locals.insert "assets" (uint256Value amount) }
      i amount cursor := by
  refine ⟨⟨h.contract, h.imms, ?_, store_get_self _ _ _, ?_, ?_⟩, ?_⟩ <;>
    rw [store_get_ne _ _ (by decide)]
  · exact h.index
  · exact h.cursor
  · exact h.queue
  · exact h.target

theorem WithdrawMorphoLocals.post {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i assets cursor : UInt256} (h : WithdrawMorphoLocals v frame i assets cursor) :
    WithdrawMorphoLocals v (accruedAssetsPostFrame frame i) (i + ⟨1⟩) assets cursor :=
  ⟨h.toWithdrawLoopLocals.post, by
    rw [accruedAssetsPostFrame, store_get_ne _ _ (by decide)]; exact h.target⟩

theorem WithdrawMorphoLocals.callFailure {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i assets cursor : UInt256} (h : WithdrawMorphoLocals v frame i assets cursor) (out : ByteArray) :
    WithdrawMorphoLocals v (supplyCallFailureFrame frame out) i assets cursor :=
  h.insert "__err" (.bytes out) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem WithdrawMorphoLocals.callSuccess {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i assets cursor : UInt256} (h : WithdrawMorphoLocals v frame i assets cursor)
    (amount : UInt256) (out : ByteArray) :
    WithdrawMorphoLocals v (supplyCallSuccessFrame frame cursor assets amount out)
      i (UInt256.sub assets amount) (nextCursor cursor ⟨64⟩) := by
  have h1 := h.insert "__ret" (.tuple [uint256Value (calldataWord out 0), uint256Value (calldataWord out 32)])
    (by decide) (by decide) (by decide) (by decide) (by decide)
  exact (h1.withCursor (nextCursor cursor ⟨64⟩)).withAssets (UInt256.sub assets amount)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
