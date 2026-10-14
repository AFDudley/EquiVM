import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSource
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_008
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_011

/-! Creation-code allocator: the same source helper used by the runtime allocator. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

theorem constructorAllocationGuard (ptr size : UInt256) :
    UInt256.lor
      (UInt256.lt (ptr + UInt256.land (UInt256.lnot ⟨31⟩) (size + ⟨31⟩)) ptr)
      (UInt256.gt (ptr + UInt256.land (UInt256.lnot ⟨31⟩) (size + ⟨31⟩))
        (UInt256.sub (UInt256.shiftLeft ⟨1⟩ ⟨64⟩) ⟨1⟩)) = ⟨0⟩ ↔ allocationFits ptr size := by
  rw [u256_land_comm (UInt256.lnot ⟨31⟩) (size + ⟨31⟩), u256_lor_comm]
  exact allocationGuard_eq_zero_iff ptr size

set_option maxRecDepth 2000 in
theorem constructorAllocateReturn {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr size ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hfit : allocationFits ptr size)
    (hret : (D_J metaMorphoV1_1CreationBytecode 0).contains ret = true)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨2608⟩
      (ptr :: size :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ret R
      (writeWord mem 64 (nextCursor ptr size)) aw' rdata σ k' C' := by
  have hnext := metaMorphoV1_1Creation_block_2608_fallthrough
    (by simp only [List.length_cons]; omega)
    ((constructorAllocationGuard ptr size).mpr hfit) rd
  obtain ⟨aw', k', C', hdone⟩ := metaMorphoV1_1Creation_block_2639_packed
    (by omega) hret hnext
  refine ⟨aw', k', C', ?_⟩
  change RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ret R
    (writeWord mem 64 (ptr + UInt256.land (UInt256.lnot ⟨31⟩) (size + ⟨31⟩)))
    aw' rdata σ k' C' at hdone
  rw [u256_land_comm] at hdone
  exact hdone

set_option maxRecDepth 2000 in
theorem constructorAllocateRevert {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr size ret : UInt256} {R : List UInt256}
    (hstack : R.length + 6 ≤ 1024) (hfit : ¬ allocationFits ptr size)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨2608⟩
      (ptr :: size :: ret :: R) mem aw rdata σ k C) :
    RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0 := by
  have hpanic := metaMorphoV1_1Creation_block_2608_taken
    (by simp only [List.length_cons]; omega)
    (fun hguard => hfit ((constructorAllocationGuard ptr size).mp hguard))
    (by native_decide) rd
  exact metaMorphoV1_1Creation_block_1854
    (by simp only [metaMorphoV1_1Creation_block_2608_taken_stack, List.length_cons]; omega)
    hpanic

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
