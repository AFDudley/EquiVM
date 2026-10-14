import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorShortLiteral

/-! Encode the fixed EIP-712 literals after storing the ERC4626 immutable words. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

theorem constructorDomainLiterals {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (hlo : 480 ≤ a.stringsEnd)
    (hptr : a.stringsEnd + 160 < UInt256.size) (hmem : a.stringsEnd + 160 ≤ mem.size)
    (hempty : memLoad (UInt256.ofNat a.stringsEnd) mem = ⟨0⟩)
    (hemptyWord : memLoad (UInt256.ofNat (a.stringsEnd + 32)) mem = ⟨0⟩)
    (hversion : memLoad (UInt256.ofNat (a.stringsEnd + 96)) mem = ⟨1⟩)
    (hversionWord : memLoad (UInt256.ofNat (a.stringsEnd + 128)) mem =
      UInt256.shiftLeft (UInt256.ofNat 49) ⟨248⟩)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨2802⟩
      (UInt256.ofNat a.stringsEnd :: ⟨466⟩ :: constructorMetadataTail a a.stringsEnd true)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨479⟩
      (constructorVersionWord :: constructorMetadataTail a a.stringsEnd true)
      (writeWord mem 352 ⟨0⟩) aw' rdata σ k' C' := by
  have hew : memLoad (UInt256.ofNat a.stringsEnd + UInt256.ofNat 32) mem = ⟨0⟩ := by
    rw [ofNat_add_words]
    exact hemptyWord
  obtain ⟨_, _, _, r1⟩ := constructorShortLiteral
    (ptr := UInt256.ofNat a.stringsEnd) (mem := mem) (ret := ⟨466⟩) (data := ⟨0⟩)
    false 0 (by simp [constructorMetadataTail])
    (by decide) hempty hew (by native_decide) rd
  rw [show UInt256.ofNat 0 = ⟨0⟩ from rfl, constructorShortStringWord_empty] at r1
  obtain ⟨_, _, _, r2⟩ := metaMorphoV1_1Creation_block_466_packed
    (by simp) (by native_decide) r1
  have hv : memLoad (UInt256.ofNat (a.stringsEnd + 96)) (writeWord mem 352 ⟨0⟩) = ⟨1⟩ := by
    rw [Reasoning.Theory.writeWord, memLoad_write_disjoint _ _ _ _
      (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)
      (.inr (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)), hversion]
  have hw : memLoad (UInt256.ofNat (a.stringsEnd + 96) + UInt256.ofNat 32)
      (writeWord mem 352 ⟨0⟩) = UInt256.shiftLeft (UInt256.ofNat 49) ⟨248⟩ := by
    rw [ofNat_add_words, show a.stringsEnd + 96 + 32 = a.stringsEnd + 128 by omega]
    rw [Reasoning.Theory.writeWord, memLoad_write_disjoint _ _ _ _
      (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)
      (.inr (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)), hversionWord]
  obtain ⟨aw3, k3, C3, r3⟩ := constructorShortLiteral
    (ptr := UInt256.ofNat (a.stringsEnd + 96)) (mem := writeWord mem 352 ⟨0⟩) (ret := ⟨479⟩)
    (data := UInt256.shiftLeft (UInt256.ofNat 49) ⟨248⟩) true 1 (by simp)
    (by decide) hv hw (by native_decide) r2
  exact ⟨aw3, k3, C3, by simpa only [show UInt256.ofNat 1 = ⟨1⟩ from rfl,
    constructorShortStringWord_version] using r3⟩

end Benchmarks.Morpho.MetaMorphoV1_1
