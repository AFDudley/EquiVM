import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorUnderlying
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_012
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_014

/-! Short-string encoding for the constructor's empty name and one-byte version. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

def constructorShortStringWord (len data : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land
    (UInt256.shiftLeft (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft (UInt256.sub ⟨32⟩ len) ⟨3⟩)) data) len

def constructorVersionWord : UInt256 :=
  ⟨0x3100000000000000000000000000000000000000000000000000000000000001⟩

theorem constructorShortStringWord_empty : constructorShortStringWord ⟨0⟩ ⟨0⟩ = ⟨0⟩ := by decide

theorem constructorShortStringWord_version :
    constructorShortStringWord ⟨1⟩ (UInt256.shiftLeft (UInt256.ofNat 49) ⟨248⟩) =
      constructorVersionWord := by decide

theorem constructorShortLiteral {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr ret data : UInt256} {R : List UInt256} (version : Bool) (len : Nat)
    (hstack : R.length + 9 ≤ 1024) (hsmall : len < 32)
    (hload : memLoad ptr mem = UInt256.ofNat len)
    (hdata : memLoad (ptr + UInt256.ofNat 32) mem = data)
    (hret : (D_J metaMorphoV1_1CreationBytecode 0).contains ret = true)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (if version then ⟨3174⟩ else ⟨2802⟩)
      (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ret
      (constructorShortStringWord (UInt256.ofNat len) data :: R) mem aw' rdata σ k' C' := by
  have hn : (UInt256.ofNat len).toNat = len := UInt256.toNat_ofNat_of_lt (by change len < 2 ^ 256; omega)
  have hlt : UInt256.lt (UInt256.ofNat len) (UInt256.ofNat 32) = ⟨1⟩ :=
    ult_one (by rw [hn]; exact hsmall)
  have hgt : UInt256.gt (UInt256.ofNat len) (UInt256.ofNat 31) = ⟨0⟩ :=
    ugt_zero (by rw [hn]; change len ≤ 31; omega)
  have hstep : ∃ aw1 k1 C1, RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨2845⟩
      (data :: UInt256.ofNat len :: ret :: R) mem aw1 rdata σ k1 C1 := by
    cases version with
    | false =>
      have r1 := metaMorphoV1_1Creation_block_2802_fallthrough
        (by omega) (by rw [hload, hlt]; rfl) rd
      have r2 := metaMorphoV1_1Creation_block_2816_fallthrough
        (by omega) (by rw [hload, hgt]; rfl) r1
      obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1Creation_block_2827_taken_packed
        (by simp only [List.length_cons]; omega) (by rw [hload, hlt]; decide) (by native_decide) r2
      refine ⟨aw3, k3, C3, ?_⟩
      simpa only [metaMorphoV1_1Creation_block_2827_taken_stack, hload, hdata] using r3
    | true =>
      have r1 := metaMorphoV1_1Creation_block_3174_fallthrough
        (by omega) (by rw [hload, hlt]; rfl) rd
      have r2 := metaMorphoV1_1Creation_block_3188_fallthrough
        (by omega) (by rw [hload, hgt]; rfl) r1
      obtain ⟨aw3, k3, C3, r3⟩ := metaMorphoV1_1Creation_block_3199_taken_packed
        (by simp only [List.length_cons]; omega) (by rw [hload, hlt]; decide) (by native_decide) r2
      refine ⟨aw3, k3, C3, ?_⟩
      simpa only [metaMorphoV1_1Creation_block_3199_taken_stack, hload, hdata] using r3
  obtain ⟨_, _, _, r3⟩ := hstep
  exact metaMorphoV1_1Creation_block_2845_packed (by omega) hret r3

end Benchmarks.Morpho.MetaMorphoV1_1
