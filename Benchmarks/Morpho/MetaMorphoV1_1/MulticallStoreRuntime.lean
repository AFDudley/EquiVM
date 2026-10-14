import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayIndexRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayPrefix
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_022
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_023

/-! Store a successful delegatecall result and advance the multicall loop counter. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem multicallStoreResult {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C i n : Nat}
    {value base bound : UInt256} {R : List UInt256} (v : MetaMorphoV1_1Immutables)
    (hstack : R.length + 15 ≤ 1024) (hi : i < n) (hn : 160 + 32 * n < UInt256.size)
    (hmem : 160 ≤ mem.size) (hlen : memLoad ⟨128⟩ mem = UInt256.ofNat n)
    (rd : RD (deployedRuntime v) I g s0 ⟨3975⟩
      (value :: UInt256.ofNat i :: ⟨1⟩ :: base :: bound :: UInt256.ofNat n :: ⟨128⟩ :: R)
      mem aw out σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨3877⟩
      (UInt256.ofNat (i + 1) :: base :: bound :: UInt256.ofNat n :: ⟨128⟩ :: R)
      (writeWord mem (160 + 32 * i) value) aw' out σ k' C' := by
  have hn' : n < UInt256.size := by omega
  have hi' : i < UInt256.size := by omega
  have hiw : (UInt256.ofNat i).toNat < (memLoad ⟨128⟩ mem).toNat := by
    rw [hlen, UInt256.toNat_ofNat_of_lt hi', UInt256.toNat_ofNat_of_lt hn']
    exact hi
  have r1 := metaMorphoV1_1_block_3975 (immWords := wordsOf (immStore v))
    (by omega) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨aw2, k2, C2, r2⟩ := memoryWordArrayIndex v
    (by simp only [List.length_cons]; omega) hiw
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1
  have haddr : UInt256.shiftLeft (UInt256.ofNat i) ⟨5⟩ + (⟨128⟩ : UInt256) + ⟨32⟩ =
      UInt256.ofNat (160 + 32 * i) := memoryWordArrayIndex_address 128 i (by omega)
  rw [haddr] at r2
  have r3 := metaMorphoV1_1_block_3985 (immWords := wordsOf (immStore v))
    (by omega) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
  have he : (metaMorphoV1_1_block_3985_memory (mem := mem)
      (x0 := UInt256.ofNat (160 + 32 * i)) (x1 := value)) =
      writeWord mem (160 + 32 * i) value := by
    simp only [metaMorphoV1_1_block_3985_memory,
      UInt256.toNat_ofNat_of_lt (show 160 + 32 * i < UInt256.size by omega),
      Reasoning.Theory.writeWord]
  rw [he] at r3
  have hl : memLoad ⟨128⟩ (writeWord mem (160 + 32 * i) value) = UInt256.ofNat n := by
    rw [Reasoning.Theory.writeWord, memLoad_write_disjoint mem (160 + 32 * i) ⟨128⟩ value hmem
      (.inl (by change 160 ≤ 160 + 32 * i; omega))]
    exact hlen
  obtain ⟨aw4, k4, C4, r4⟩ := memoryWordArrayIndex v
    (by simp only [List.length_cons]; omega)
    (by rw [hl, UInt256.toNat_ofNat_of_lt hi', UInt256.toNat_ofNat_of_lt hn']; exact hi)
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r3
  obtain ⟨aw5, k5, C5, r5⟩ := metaMorphoV1_1_block_3996_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r4
  refine ⟨aw5, k5, C5, ?_⟩
  have hadd : UInt256.ofNat i + (⟨1⟩ : UInt256) = UInt256.ofNat (i + 1) := ofNat_add_words i 1
  simpa only [metaMorphoV1_1_block_3996_stack, hadd] using r5

end Benchmarks.Morpho.MetaMorphoV1_1
