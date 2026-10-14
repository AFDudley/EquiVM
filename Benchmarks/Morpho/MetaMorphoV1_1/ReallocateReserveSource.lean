import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateRowAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateSyntax

/-! The two checked source reservations made before reading a reallocation row. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def reallocateReserveFrame (frame : Frame) (ptr : UInt256) : Frame :=
  { frame with locals := ((frame.locals.insert cursorName (uint256Value (nextCursor ptr ⟨64⟩))).insert
      cursorName (uint256Value (nextCursor ptr ⟨224⟩))) }

theorem reallocateReserveSource {frame : Frame} {evm : State} {ptr : UInt256}
    (hc : frame.contract = contract)
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hf : allocationFits ptr ⟨224⟩) :
    ExecBlock config frame evm [reserveBytes 64, reserveBytes 160]
      (.ok (reallocateReserveFrame frame ptr) evm) := by
  obtain ⟨hfirst, hsecond⟩ := (reallocateRowAllocationFits ptr).mp hf
  have h1 := allocateCallReturns (cfg := config) (evm := evm)
    (ptrExpr := .var cursorName) (sizeExpr := .intLit 64) cursorName
    (by rw [hc]; exact allocateFunction_lookup) (evalLocalValue hp) (by simp only [evalExpr?, pure]; rfl) hfirst
  have h2 := allocateCallReturns (cfg := config) (evm := evm)
    (frame := { frame with locals := frame.locals.insert cursorName (uint256Value (nextCursor ptr ⟨64⟩)) })
    (ptrExpr := .var cursorName) (sizeExpr := .intLit 160) cursorName
    (by change lookupCallable? frame.contract _ = _; rw [hc]; exact allocateFunction_lookup)
    (evalLocalValue (store_get_self _ _ _)) (by simp only [evalExpr?, pure]; rfl) hsecond
  rw [reallocateRowNextCursor] at h2
  exact ExecBlock.consNormal h1 (ExecBlock.consNormal h2 ExecBlock.nil)

theorem reallocateReserveRevert {frame : Frame} {evm : State} {ptr : UInt256}
    (hc : frame.contract = contract)
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (hf : ¬ allocationFits ptr ⟨224⟩) :
    ExecBlock config frame evm [reserveBytes 64, reserveBytes 160] .reverted := by
  by_cases hfirst : allocationFits ptr ⟨64⟩
  · have h1 := allocateCallReturns (cfg := config) (evm := evm)
      (ptrExpr := .var cursorName) (sizeExpr := .intLit 64) cursorName
      (by rw [hc]; exact allocateFunction_lookup) (evalLocalValue hp) (by simp only [evalExpr?, pure]; rfl) hfirst
    have hsecond : ¬ allocationFits (nextCursor ptr ⟨64⟩) ⟨160⟩ :=
      fun h ↦ hf ((reallocateRowAllocationFits ptr).mpr ⟨hfirst, h⟩)
    have h2 := allocateCallReverts (cfg := config) (evm := evm)
      (frame := { frame with locals := frame.locals.insert cursorName (uint256Value (nextCursor ptr ⟨64⟩)) })
      (ptrExpr := .var cursorName) (sizeExpr := .intLit 160) cursorName
      (by change lookupCallable? frame.contract _ = _; rw [hc]; exact allocateFunction_lookup)
      (evalLocalValue (store_get_self _ _ _)) (by simp only [evalExpr?, pure]; rfl) hsecond
    exact ExecBlock.consNormal h1 (ExecBlock.consRevert h2)
  · exact ExecBlock.consRevert (allocateCallReverts (cfg := config) (evm := evm)
      (ptrExpr := .var cursorName) (sizeExpr := .intLit 64) cursorName
      (by rw [hc]; exact allocateFunction_lookup) (evalLocalValue hp) (by simp only [evalExpr?, pure]; rfl) hfirst)

theorem reallocateReserveFrame_preserves (frame : Frame) (ptr : UInt256) (name : Ident)
    (hn : (cursorName == name) = false) :
    (reallocateReserveFrame frame ptr).locals.get? name = frame.locals.get? name := by
  simp only [reallocateReserveFrame, store_get_ne _ _ hn]

theorem reallocateReserveFrame_cursor (frame : Frame) (ptr : UInt256) :
    (reallocateReserveFrame frame ptr).locals.get? cursorName =
      some (uint256Value (nextCursor ptr ⟨224⟩)) := store_get_self _ _ _

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
