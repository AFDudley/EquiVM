import Benchmarks.Safe.V3_77901a5.Common
import Reasoning.WordArithmetic
import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_048
import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_050

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe.V3_77901a5

set_option maxRecDepth 100000

theorem safeDecrementTrace {I g s0 σ k C aw mem rdata} {value ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11526⟩ (value :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) (hnz : value ≠ ⟨0⟩)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD safeBytecode I g s0 ret (UInt256.sub value ⟨1⟩ :: R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_11526_taken (by simp; omega) hnz (by jump_dest) h
  have h₂ := safeRuntime_block_11540 (by omega) hret h₁
  simpa only [safeRuntime_block_11540_stack, lnot_zero_add] using ⟨_, _, h₂⟩

theorem safeDecrementUnderflow {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11526⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) : RDrev safeBytecode g s0 := by
  have h₁ := safeRuntime_block_11526_fallthrough (by omega) rfl h
  have h₂ := safeRuntime_block_11533
    (by simp only [safeRuntime_block_11526_fallthrough_stack, List.length_cons]; omega)
    (by jump_dest) h₁
  exact safeRuntime_block_11004
    (by simp only [safeRuntime_block_11533_stack, safeRuntime_block_11526_fallthrough_stack,
      List.length_cons]; omega) h₂

end Benchmarks.Safe.V3_77901a5
