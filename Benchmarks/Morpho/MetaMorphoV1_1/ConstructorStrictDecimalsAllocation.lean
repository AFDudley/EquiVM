import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorEncoding
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_005
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_006
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_007

/-! Failed calls, short returns, and the bounded strict-decimals return allocation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

theorem constructorStrictDecimalsFailure {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (hout : out.size < UInt256.size)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1040⟩
      [⟨0⟩, ptr, UInt256.ofNat a.asset.val, UInt256.ofNat a.morpho.val, ⟨32⟩, ⟨64⟩]
      mem aw out σ k C) : RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0 := by
  have r1 := metaMorphoV1_1Creation_block_1040_taken (by simp) (by decide +kernel) (by native_decide) rd
  exact metaMorphoV1_1Creation_block_1607 (by simp)
    (by change 0 + (UInt256.ofNat out.size).toNat ≤ out.size
        rw [UInt256.toNat_ofNat_of_lt hout, Nat.zero_add]) r1

theorem constructorStrictDecimalsAllocation {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (hout : out.size < UInt256.size)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1040⟩
      [⟨1⟩, ptr, UInt256.ofNat a.asset.val, UInt256.ofNat a.morpho.val, ⟨32⟩, ⟨64⟩]
      mem aw out σ k C) :
    (¬ (32 ≤ out.size ∧ allocationFits ptr ⟨32⟩) ∧
      RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    (32 ≤ out.size ∧ allocationFits ptr ⟨32⟩ ∧ ∃ aw' k' C',
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1579⟩
        [ptr, UInt256.ofNat a.asset.val, UInt256.ofNat a.morpho.val, ⟨32⟩, ⟨64⟩]
        (writeWord mem 64 (nextCursor ptr ⟨32⟩)) aw' out σ k' C') := by
  have r1 := metaMorphoV1_1Creation_block_1040_fallthrough (by simp) (by decide +kernel) rd
  have r2 := metaMorphoV1_1Creation_block_1047_taken (by simp) (by decide +kernel) (by native_decide) r1
  by_cases hl : 32 ≤ out.size
  · have r3 := metaMorphoV1_1Creation_block_1547_fallthrough (by simp)
      (ugt_zero (by simpa only [UInt256.toNat_ofNat_of_lt hout] using hl)) r2
    have r4 := metaMorphoV1_1Creation_block_1560 (by simp) (by native_decide) r3
    by_cases hf : allocationFits ptr ⟨32⟩
    · obtain ⟨_, _, _, r5⟩ := constructorAllocateReturn (by simp) hf (by native_decide) r4
      obtain ⟨aw6, k6, C6, r6⟩ := metaMorphoV1_1Creation_block_1570_fallthrough_packed (by simp) (by rw [word_add_sub_left]; decide +kernel) r5
      exact .inr ⟨hl, hf, aw6, k6, C6, r6⟩
    · exact .inl ⟨fun h => hf h.2, constructorAllocateRevert (by simp) hf r4⟩
  · have r3 := metaMorphoV1_1Creation_block_1547_taken (by simp)
      (by rw [ugt_one (by simpa only [UInt256.toNat_ofNat_of_lt hout] using
            Nat.lt_of_not_ge hl)]; decide) (by native_decide) r2
    have r4 := metaMorphoV1_1Creation_block_1600 (by simp) (by native_decide) r3
    have r5 := metaMorphoV1_1Creation_block_1560 (by simp) (by native_decide) r4
    refine .inl ⟨fun h => hl h.1, ?_⟩
    by_cases hf : allocationFits ptr (UInt256.ofNat out.size)
    · obtain ⟨_, _, _, r6⟩ := constructorAllocateReturn (by simp) hf (by native_decide) r5
      have r7 := metaMorphoV1_1Creation_block_1570_taken (by simp)
        (by
          have hshort : UInt256.slt (UInt256.ofNat out.size) ⟨32⟩ = ⟨1⟩ :=
            slt_ofNat_lit_one_low (n := out.size) (m := 32) (by decide +kernel) (by omega)
          rw [word_add_sub_left, hshort]; decide +kernel)
        (by native_decide) r6
      exact metaMorphoV1_1Creation_block_1596
        (by simp [metaMorphoV1_1Creation_block_1570_taken_stack]) r7
    · exact constructorAllocateRevert (by simp) hf r5

theorem constructorStrictDecimalsRead {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem out : ByteArray} {aw ptr word : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (hword : memLoad ptr mem = word)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1579⟩
      [ptr, UInt256.ofNat a.asset.val, UInt256.ofNat a.morpho.val, ⟨32⟩, ⟨64⟩]
      mem aw out σ k C) :
    (¬ word.toNat < 256 ∧ RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    (word.toNat < 256 ∧ ∃ aw' k' C',
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1053⟩
        [⟨255⟩, word, UInt256.ofNat a.asset.val, UInt256.ofNat a.morpho.val, ⟨32⟩, ⟨64⟩]
        mem aw' out σ k' C') := by
  by_cases hv : word.toNat < 256
  · have r1 := metaMorphoV1_1Creation_block_1579_fallthrough (by simp)
      (by
        have hm : word.land (UInt256.ofNat 255) = word := lowByteClean hv
        rw [hword, hm]; exact u256_sub_eq_zero_iff_eq.mpr rfl) rd
    obtain ⟨aw2, k2, C2, r2⟩ := metaMorphoV1_1Creation_block_1590_packed
      (by simp [metaMorphoV1_1Creation_block_1579_fallthrough_stack]) (by native_decide) r1
    exact .inr ⟨hv, aw2, k2, C2, by simpa only
      [metaMorphoV1_1Creation_block_1590_stack, metaMorphoV1_1Creation_block_1579_fallthrough_stack,
        hword] using r2⟩
  · have r1 := metaMorphoV1_1Creation_block_1579_taken (by simp)
      (by rw [hword]; intro hz
          exact hv ((lowByteClean_iff _).mp (u256_sub_eq_zero_iff_eq.mp hz).symm))
      (by native_decide) rd
    exact .inl ⟨hv, metaMorphoV1_1Creation_block_1596
      (by simp [metaMorphoV1_1Creation_block_1579_taken_stack]) r1⟩

end Benchmarks.Morpho.MetaMorphoV1_1
