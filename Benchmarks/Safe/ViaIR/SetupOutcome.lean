import Benchmarks.Safe.ViaIR.SetupSource

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

inductive SetupOutcome (frame : Frame) (evm : State) (body : List Stmt)
    (g : Sat256) (s0 : State) : Prop where
  | reverted (source : ExecBlock config frame evm body .reverted)
      (trace : RDrev safeBytecode g s0)
  | staticHalt (source : ExecBlock config frame evm body .staticViolation)
      (trace : RDstatic safeBytecode g s0)
  | success {frame' evm'} (source : ExecBlock config frame evm body (.ok frame' evm'))
      (trace : RDret safeBytecode g s0 evm'.accountMap ByteArray.empty)

/-- A setup tail either establishes the local allocation guard or reports its failure. -/
inductive SetupTailOutcome (p : SetupInput) (frame : Frame) (evm : State) (body : List Stmt)
    (g : Sat256) (s0 : State) : Prop where
  | allocationRevert (bound : ¬32 * p.owners.length + p.payload.size ≤ p.allocationLimit)
      (trace : RDrev safeBytecode g s0)
  | reverted (source : ExecBlock config frame evm body .reverted)
      (trace : RDrev safeBytecode g s0)
  | success {frame' evm'} (bound : 32 * p.owners.length + p.payload.size ≤ p.allocationLimit)
      (source : ExecBlock config frame evm body (.ok frame' evm'))
      (trace : RDret safeBytecode g s0 evm'.accountMap ByteArray.empty)

theorem SetupTailOutcome.prepend {p frame frame' evm evm' stmt body g s0}
    (h : SetupTailOutcome p frame' evm' body g s0)
    (hs : ExecStmt config frame evm stmt (.ok frame' evm')) :
    SetupTailOutcome p frame evm (stmt :: body) g s0 := by
  cases h with
  | allocationRevert bound trace => exact .allocationRevert bound trace
  | reverted source trace => exact .reverted (.consNormal hs source) trace
  | success bound source trace => exact .success bound (.consNormal hs source) trace

end Benchmarks.Safe.ViaIR
