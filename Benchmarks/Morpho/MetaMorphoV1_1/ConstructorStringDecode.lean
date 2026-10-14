import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorArgumentMemory
import Benchmarks.Morpho.MetaMorphoV1_1.StringEncoderRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_012

/-! The creation code's shared string decoder, including allocation failure. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

theorem constructorStringAllocator {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256} (src stop len : Nat)
    (hstack : R.length + 11 ≤ 1024) (hlen : len < 2 ^ 64)
    (hhead : src + 32 ≤ stop) (hstop : stop < 2 ^ 255)
    (hload : memLoad (UInt256.ofNat src) mem = UInt256.ofNat len)
    (hfree : memLoad ⟨64⟩ mem = ptr)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨2690⟩
      (UInt256.ofNat src :: UInt256.ofNat stop :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨2608⟩
      (ptr :: UInt256.ofNat (32 + paddedSize len) :: ⟨2727⟩ :: UInt256.ofNat stop ::
        UInt256.ofNat src :: UInt256.ofNat len :: ptr :: ret :: R) mem aw' rdata σ k' C' := by
  change memLoad (UInt256.ofNat 64) mem = ptr at hfree
  have hls : len < UInt256.size := by change len < 2 ^ 256; omega
  have hguard : UInt256.isZero
      (UInt256.slt (UInt256.ofNat src + UInt256.ofNat 31) (UInt256.ofNat stop)) = ⟨0⟩ := by
    rw [ofNat_add_words, slt_ofNat_lit_one_low hstop (by omega)]
    rfl
  have r1 := metaMorphoV1_1Creation_block_2690_fallthrough
    (by simp only [List.length_cons]; omega) hguard rd
  have r2 := metaMorphoV1_1Creation_block_2702
    (by simp only [List.length_cons]; omega) (by native_decide) r1
  simp only [metaMorphoV1_1Creation_block_2702_stack, hload] at r2
  have r3 := metaMorphoV1_1Creation_block_2663_fallthrough
    (by simp only [List.length_cons]; omega)
    (ugt_zero (by change (UInt256.ofNat len).toNat ≤ 2 ^ 64 - 1
                  rw [UInt256.toNat_ofNat_of_lt hls]; omega)) r2
  have r4 := metaMorphoV1_1Creation_block_2678
    (by simp only [List.length_cons]; omega) (by native_decide) r3
  have hround := stringEncoderRoundedSize (UInt256.ofNat len) (by
    rw [UInt256.toNat_ofNat_of_lt hls]; omega)
  rw [UInt256.toNat_ofNat_of_lt hls] at hround
  simp only [metaMorphoV1_1Creation_block_2678_stack] at r4
  rw [hround, ofNat_add_words] at r4
  obtain ⟨aw', k', C', r5⟩ := metaMorphoV1_1Creation_block_2713_packed
    (by simp only [List.length_cons]; omega) (by native_decide) r4
  refine ⟨aw', k', C', ?_⟩
  simpa only [metaMorphoV1_1Creation_block_2713_stack, hfree] using r5

theorem constructorStringAllocationRevert {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256} (src stop len : Nat)
    (hstack : R.length + 11 ≤ 1024) (hlen : len < 2 ^ 64)
    (hhead : src + 32 ≤ stop) (hstop : stop < 2 ^ 255)
    (hload : memLoad (UInt256.ofNat src) mem = UInt256.ofNat len)
    (hfree : memLoad ⟨64⟩ mem = ptr)
    (hfit : ¬ allocationFits ptr (UInt256.ofNat (32 + paddedSize len)))
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨2690⟩
      (UInt256.ofNat src :: UInt256.ofNat stop :: ret :: R) mem aw rdata σ k C) :
    RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0 := by
  obtain ⟨_, _, _, r1⟩ := constructorStringAllocator src stop len
    hstack hlen hhead hstop hload hfree rd
  exact constructorAllocateRevert (by simp only [List.length_cons]; omega) hfit r1

set_option maxRecDepth 2000 in
theorem constructorStringReturn {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256} (src stop len : Nat)
    (hstack : R.length + 11 ≤ 1024) (hlen : len < 2 ^ 64)
    (hwindow : src + 32 + len ≤ stop) (hstop : stop < 2 ^ 255)
    (hload : memLoad (UInt256.ofNat src) mem = UInt256.ofNat len)
    (hfree : memLoad ⟨64⟩ mem = ptr)
    (hfit : allocationFits ptr (UInt256.ofNat (32 + paddedSize len)))
    (hret : (D_J metaMorphoV1_1CreationBytecode 0).contains ret = true)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨2690⟩
      (UInt256.ofNat src :: UInt256.ofNat stop :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ret (ptr :: R)
      (stringPayloadMemory (writeWord mem 64
        (nextCursor ptr (UInt256.ofNat (32 + paddedSize len))))
        (src + 32) ptr.toNat (UInt256.ofNat len)) aw' rdata σ k' C' := by
  have hp : ptr.toNat < 2 ^ 64 := by
    have := (allocationFits_iff_sum_lt _ _).mp hfit
    omega
  have hls : len < UInt256.size := by change len < 2 ^ 256; omega
  have hes : stop < UInt256.size := lt_size_of_lt_sign hstop
  obtain ⟨_, _, _, r1⟩ := constructorStringAllocator src stop len hstack hlen
    (by omega) hstop hload hfree rd
  obtain ⟨_, _, _, r2⟩ := constructorAllocateReturn
    (by simp only [List.length_cons]; omega) hfit (by native_decide) r1
  have hguard : UInt256.gt
      ((UInt256.ofNat src + UInt256.ofNat len) + UInt256.ofNat 32)
      (UInt256.ofNat stop) = ⟨0⟩ := by
    apply ugt_zero
    rw [ofNat_add_words, ofNat_add_words,
      UInt256.toNat_ofNat_of_lt (by omega), UInt256.toNat_ofNat_of_lt hes]
    omega
  have r3 := metaMorphoV1_1Creation_block_2727_fallthrough
    (by simp only [List.length_cons]; omega) hguard r2
  obtain ⟨aw', k', C', r4⟩ := metaMorphoV1_1Creation_block_2742_packed
    (by omega) hret r3
  have hs : (UInt256.ofNat src + UInt256.ofNat 32).toNat = src + 32 := by
    rw [ofNat_add_words, UInt256.toNat_ofNat_of_lt (by omega)]
  have hd : (ptr + UInt256.ofNat 32).toNat = ptr.toNat + 32 := by
    rw [uadd_toNat]
    exact Nat.mod_eq_of_lt (by change ptr.toNat + 32 < 2 ^ 256; omega)
  have hz : ((ptr + UInt256.ofNat len) + UInt256.ofNat 32).toNat =
      ptr.toNat + 32 + (UInt256.ofNat len).toNat := by
    conv_lhs => rw [← u256_ofNat_toNat ptr]
    rw [ofNat_add_words, ofNat_add_words,
      UInt256.toNat_ofNat_of_lt (by change ptr.toNat + len + 32 < 2 ^ 256; omega),
      UInt256.toNat_ofNat_of_lt hls]
    omega
  refine ⟨aw', k', C', ?_⟩
  simpa only [metaMorphoV1_1Creation_block_2742_stack,
    metaMorphoV1_1Creation_block_2742_memory,
    metaMorphoV1_1Creation_block_2727_fallthrough_memory, hs, hd, hz,
    stringPayloadMemory, stringPayloadCopy, Reasoning.Theory.writeWord] using r4

end Benchmarks.Morpho.MetaMorphoV1_1
