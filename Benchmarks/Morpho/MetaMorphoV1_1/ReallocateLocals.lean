import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateRowSource
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateReserveSource
import Benchmarks.Morpho.MetaMorphoV1_1.CursorCallSource

/-! The source locals retained between iterations of the reallocation loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
attribute [local irreducible] contract

structure ReallocateLocals (v : MetaMorphoV1_1Immutables) (frame : Frame) (values : List Value)
    (i supplied withdrawn cursor : UInt256) : Prop where
  contract : frame.contract = contract
  imms : frame.immutables = immStore v
  config : frame.locals.get? "config" = none
  input : frame.locals.get? "allocations" = some (.array values)
  index : frame.locals.get? "i" = some (uint256Value i)
  supplied : frame.locals.get? "totalSupplied" = some (uint256Value supplied)
  withdrawn : frame.locals.get? "totalWithdrawn" = some (uint256Value withdrawn)
  cursor : frame.locals.get? cursorName = some (uint256Value cursor)
  target : frame.locals.get? "morphoTarget" = some (.address v.MORPHO)

def reallocateProtectedLocals : List Ident :=
  ["config", "allocations", "i", "totalSupplied", "totalWithdrawn", cursorName, "morphoTarget"]

theorem ReallocateLocals.insert {v : MetaMorphoV1_1Immutables} {frame : Frame} {values : List Value}
    {i supplied withdrawn cursor : UInt256} (h : ReallocateLocals v frame values i supplied withdrawn cursor)
    (name : Ident) (value : Value) (hn : name ∉ reallocateProtectedLocals) :
    ReallocateLocals v { frame with locals := frame.locals.insert name value }
      values i supplied withdrawn cursor := by
  have hne (key : Ident) (hk : key ∈ reallocateProtectedLocals) : (name == key) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro heq
    exact hn (heq ▸ hk)
  refine ⟨h.contract, h.imms, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [store_get_ne _ _ (hne "config" (by decide))]; exact h.config
  · rw [store_get_ne _ _ (hne "allocations" (by decide))]; exact h.input
  · rw [store_get_ne _ _ (hne "i" (by decide))]; exact h.index
  · rw [store_get_ne _ _ (hne "totalSupplied" (by decide))]; exact h.supplied
  · rw [store_get_ne _ _ (hne "totalWithdrawn" (by decide))]; exact h.withdrawn
  · rw [store_get_ne _ _ (hne cursorName (by decide))]; exact h.cursor
  · rw [store_get_ne _ _ (hne "morphoTarget" (by decide))]; exact h.target

theorem ReallocateLocals.withCursor {v : MetaMorphoV1_1Immutables} {frame : Frame} {values : List Value}
    {i supplied withdrawn cursor : UInt256} (h : ReallocateLocals v frame values i supplied withdrawn cursor)
    (ptr : UInt256) :
    ReallocateLocals v { frame with locals := frame.locals.insert cursorName (uint256Value ptr) }
      values i supplied withdrawn ptr := by
  refine ⟨h.contract, h.imms, ?_, ?_, ?_, ?_, ?_, store_get_self _ _ _, ?_⟩
  all_goals rw [store_get_ne _ _ (by decide)]
  · exact h.config
  · exact h.input
  · exact h.index
  · exact h.supplied
  · exact h.withdrawn
  · exact h.target

theorem ReallocateLocals.withSupplied {v : MetaMorphoV1_1Immutables} {frame : Frame} {values : List Value}
    {i supplied withdrawn cursor : UInt256} (h : ReallocateLocals v frame values i supplied withdrawn cursor)
    (amount : UInt256) :
    ReallocateLocals v { frame with locals := frame.locals.insert "totalSupplied" (uint256Value amount) }
      values i amount withdrawn cursor := by
  refine ⟨h.contract, h.imms, ?_, ?_, ?_, store_get_self _ _ _, ?_, ?_, ?_⟩
  all_goals rw [store_get_ne _ _ (by decide)]
  · exact h.config
  · exact h.input
  · exact h.index
  · exact h.withdrawn
  · exact h.cursor
  · exact h.target

theorem ReallocateLocals.withWithdrawn {v : MetaMorphoV1_1Immutables} {frame : Frame} {values : List Value}
    {i supplied withdrawn cursor : UInt256} (h : ReallocateLocals v frame values i supplied withdrawn cursor)
    (amount : UInt256) :
    ReallocateLocals v { frame with locals := frame.locals.insert "totalWithdrawn" (uint256Value amount) }
      values i supplied amount cursor := by
  refine ⟨h.contract, h.imms, ?_, ?_, ?_, ?_, store_get_self _ _ _, ?_, ?_⟩
  all_goals rw [store_get_ne _ _ (by decide)]
  · exact h.config
  · exact h.input
  · exact h.index
  · exact h.supplied
  · exact h.cursor
  · exact h.target

theorem ReallocateLocals.withIndex {v : MetaMorphoV1_1Immutables} {frame : Frame} {values : List Value}
    {i supplied withdrawn cursor : UInt256} (h : ReallocateLocals v frame values i supplied withdrawn cursor)
    (index : UInt256) :
    ReallocateLocals v { frame with locals := frame.locals.insert "i" (uint256Value index) }
      values index supplied withdrawn cursor := by
  refine ⟨h.contract, h.imms, ?_, ?_, store_get_self _ _ _, ?_, ?_, ?_, ?_⟩
  all_goals rw [store_get_ne _ _ (by decide)]
  · exact h.config
  · exact h.input
  · exact h.supplied
  · exact h.withdrawn
  · exact h.cursor
  · exact h.target

theorem ReallocateLocals.reserve {v : MetaMorphoV1_1Immutables} {frame : Frame} {values : List Value}
    {i supplied withdrawn cursor : UInt256} (h : ReallocateLocals v frame values i supplied withdrawn cursor) :
    ReallocateLocals v (reallocateReserveFrame frame cursor) values i supplied withdrawn
      (nextCursor cursor ⟨224⟩) :=
  (h.withCursor (nextCursor cursor ⟨64⟩)).withCursor (nextCursor cursor ⟨224⟩)

theorem ReallocateLocals.row {v : MetaMorphoV1_1Immutables} {frame : Frame} {values : List Value}
    {i supplied withdrawn cursor : UInt256} (h : ReallocateLocals v frame values i supplied withdrawn cursor)
    (row : ByteArray) :
    ReallocateLocals v (reallocateRowFrame frame row) values i supplied withdrawn cursor :=
  (((h.insert "allocationTuple" (reallocateRowValue row) (by decide)).insert
    "paramsTuple" (.tuple (marketParamsFields row)) (by decide)).insert
      "params" (marketParamsData row).value (by decide)).insert
        "allocation" (reallocateAllocationValue row) (by decide)

theorem ReallocateLocals.identified {v : MetaMorphoV1_1Immutables} {frame : Frame} {values : List Value}
    {i supplied withdrawn cursor : UInt256} (h : ReallocateLocals v frame values i supplied withdrawn cursor)
    (row : ByteArray) :
    ReallocateLocals v (reallocateIdentifiedFrame frame row) values i supplied withdrawn cursor :=
  (h.row row).insert "id" (wordBytes32Value (marketParamsData row).id) (by decide)

theorem ReallocateLocals.reader {v : MetaMorphoV1_1Immutables} {frame : Frame} {values : List Value}
    {i supplied withdrawn cursor : UInt256} (h : ReallocateLocals v frame values i supplied withdrawn cursor)
    (name : Ident) (value : Value) (ptr : UInt256) (hn : name ∉ reallocateProtectedLocals) :
    ReallocateLocals v (cursorResultFrame frame name value ptr) values i supplied withdrawn ptr :=
  (((h.insert slotsAndCursorName (.tuple [value, uint256Value ptr]) (by decide)).insert
    name value hn).withCursor ptr)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
