import Benchmarks.Safe.ViaIR.Blocks.Runtime_030
import Benchmarks.Safe.ViaIR.Routines
import Benchmarks.Safe.ViaIR.MemoryBytesDecoded

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000 in
theorem safeReturnBoolFromMemory {I g s0 σ k C rdata aw mem} {b : Bool} {ptr : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨6377⟩ (b.toUInt256 :: ⟨32⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) (hf : memLoad ⟨64⟩ mem = ptr)
    (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr.toNat) :
    RDret safeBytecode g s0 σ b.toUInt256.toByteArray := by
  have hbool : UInt256.isZero (UInt256.isZero b.toUInt256) = b.toUInt256 := by
    cases b <;> rfl
  have hr := safeRuntime_block_6377 hov h
  change memLoad (UInt256.ofNat 64) mem = ptr at hf
  simp only [hbool, hf] at hr
  change RDret safeBytecode g s0 σ
    ((writeWord mem ptr.toNat b.toUInt256).readWithPadding ptr.toNat 32) at hr
  simpa only [writeWord_sparse_read_back] using hr

end Benchmarks.Safe.ViaIR
