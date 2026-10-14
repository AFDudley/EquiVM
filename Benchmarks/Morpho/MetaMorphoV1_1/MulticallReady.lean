import Benchmarks.Morpho.MetaMorphoV1_1.DelegateCallSource
import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayAllocationSource
import Benchmarks.EAS.Attester.LocalArray

/-! Source-frame facts for the allocated multicall loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
set_option maxRecDepth 2000

def multicallLoopCondition : Expr := .binary .lt (.var "i") multicallLength

def multicallLoopPost : List Stmt :=
  [.assign .localVar ⟨"i", []⟩ (.inRange (.uint ⟨256, by decide⟩)
    (.binary .add (.var "i") (.intLit 1)))]

def multicallLoopBody : List Stmt :=
  match allocatedMulticallLoop with | .for _ _ _ body => body | _ => []

structure MulticallReady (frame : Frame) (imms : Store) (data : List Value)
    (results : List ByteArray) (i : Nat) (ptr : UInt256) : Prop where
  contract : frame.contract = MetaMorphoV1_1.contract
  immutables : frame.immutables = imms
  input : frame.locals.get? "data" = some (.array data)
  results : frame.locals.get? "results" = some (.array (results.map Value.bytes))
  index : frame.locals.get? "i" = some (.int (Int.ofNat i))
  cursor : frame.locals.get? cursorName = some (uint256Value ptr)

def multicallIndexFrame (frame : Frame) (i : Nat) : Frame :=
  { frame with locals := frame.locals.insert "i" (.int (Int.ofNat i)) }

theorem MulticallReady.indexFrame {frame : Frame} {imms : Store} {data : List Value}
    {results : List ByteArray} {i : Nat} {ptr : UInt256}
    (h : MulticallReady frame imms data results i ptr) (j : Nat) :
    MulticallReady (multicallIndexFrame frame j) imms data results j ptr := by
  constructor
  · exact h.contract
  · exact h.immutables
  · rw [multicallIndexFrame, store_get_ne _ _ (by decide)]; exact h.input
  · rw [multicallIndexFrame, store_get_ne _ _ (by decide)]; exact h.results
  · exact store_get_self _ _ _
  · rw [multicallIndexFrame, store_get_ne _ _ (by decide)]; exact h.cursor

theorem multicallConditionSource {frame : Frame} {imms : Store} {evm : State}
    {data : List Value} {results : List ByteArray} {i : Nat} {ptr : UInt256}
    (h : MulticallReady frame imms data results i ptr) :
    evalExpr? config frame evm multicallLoopCondition = .ok (.bool (decide (i < data.length))) :=
  naturalLtSource (evalLocalValue h.index) (evalLocalArrayLength h.input)

theorem multicallPostSource {frame : Frame} {imms : Store} {evm : State}
    {data : List Value} {results : List ByteArray} {i : Nat} {ptr : UInt256}
    (h : MulticallReady frame imms data results i ptr) (hi : i + 1 < UInt256.size) :
    ExecBlock config frame evm multicallLoopPost (.ok (multicallIndexFrame frame (i + 1)) evm) :=
  execLocalIncrement h.index hi

def multicallReadFrame (frame : Frame) (value : Value) : Frame :=
  { frame with locals := frame.locals.insert "__solcDelegateData" value }

def multicallCopyFrame (frame : Frame) (data : ByteArray) (ptr : UInt256) : Frame :=
  let f := multicallReadFrame frame (.bytes data)
  { f with locals := f.locals.insert cursorName (uint256Value (bytesAllocPtr ptr data.size)) }

def multicallCallFrame (frame : Frame) (data : ByteArray) (ptr : UInt256) (out : ByteArray) : Frame :=
  let f := multicallCopyFrame frame data ptr
  { f with
    locals := f.locals.insert "__solcDelegateResult"
      (.tuple [.bytes out, uint256Value (callReturnCursor (bytesAllocPtr ptr data.size) out)]) }

def multicallResultFrame (frame : Frame) (data : ByteArray) (ptr : UInt256) (out : ByteArray) : Frame :=
  let f := multicallCallFrame frame data ptr out
  { f with
    locals := (f.locals.insert "__c0" (.bytes out)).insert cursorName
      (uint256Value (callReturnCursor (bytesAllocPtr ptr data.size) out)) }

def multicallStepFrame (frame : Frame) (data : ByteArray) (ptr : UInt256) (out : ByteArray)
    (results : List ByteArray) (i : Nat) : Frame :=
  let f := multicallResultFrame frame data ptr out
  { f with locals := f.locals.insert "results" (.array ((results.set i out).map Value.bytes)) }

theorem MulticallReady.stepFrame {frame : Frame} {imms : Store} {data : List Value}
    {results : List ByteArray} {i : Nat} {ptr : UInt256}
    (h : MulticallReady frame imms data results i ptr) (input out : ByteArray) :
    MulticallReady (multicallStepFrame frame input ptr out results i) imms data
      (results.set i out) i (callReturnCursor (bytesAllocPtr ptr input.size) out) := by
  constructor <;> simp only [multicallStepFrame, multicallResultFrame, multicallCallFrame,
    multicallCopyFrame, multicallReadFrame]
  all_goals repeat first | rw [store_get_self] | rw [store_get_ne _ _ (by decide)]
  all_goals first | exact h.contract | exact h.immutables | exact h.input | exact h.index

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
