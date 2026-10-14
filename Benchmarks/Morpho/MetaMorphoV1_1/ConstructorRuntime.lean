import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorRuntimeParts

/-! The deployment tail returns the runtime template patched with every constructor immutable. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem constructorRuntime {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw ptr x0 x1 x2 x3 : UInt256}
    {σ : AccountMap} {k C : Nat} (hm : 480 ≤ mem.size) (hlo : 480 ≤ ptr.toNat)
    (hbound : ptr.toNat < 2 ^ 64) (hptr : memLoad ⟨64⟩ mem = ptr)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1153⟩
      [x0, x1, x2, x3, ⟨64⟩] mem aw rdata σ k C) :
    RDret (metaMorphoV1_1CreationBytecode ++ tail) g s0 σ
      (immutableLayout.runtime metaMorphoV1_1Bytecode
        (constructorRuntimeWords (fun off ↦ memLoad (UInt256.ofNat off) mem))) := by
  let w := fun off ↦ memLoad (UInt256.ofNat off) mem
  have hfit : ptr.toNat + 19708 < UInt256.size := by change _ < 2 ^ 256; omega
  have hr (off : Nat) (_ : 128 ≤ off) (_ : off + 32 ≤ 480) : memLoad (UInt256.ofNat off) mem = w off := rfl
  have hc := constructorRuntimeCopy_prefix mem tail ptr
  have hp1 := hc.trans (constructorRuntimePart_prefix (constructorRuntimeCopy mem tail ptr) ptr w 0 9)
  have hm1 : 480 ≤ (constructorRuntimePart (constructorRuntimeCopy mem tail ptr) ptr w 0 9).size :=
    le_trans hm hp1.size
  have hr1 (off : Nat) (h1 : 128 ≤ off) (h2 : off + 32 ≤ 480) :
      memLoad (UInt256.ofNat off) (constructorRuntimePart (constructorRuntimeCopy mem tail ptr) ptr w 0 9) =
        w off :=
    hp1.load_preserved (by omega) (by omega) (by omega) (by omega)
  obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_1153_packed (by simp) rd
  obtain ⟨hs1, he1⟩ := constructorRuntimeStart_eq (tail := tail) hm hlo hfit hptr hr x0 x1 x2 x3 []
  rw [hs1, he1] at r1
  have he2 := constructorRuntimeMiddle_eq hm1 hlo hfit hr1 [⟨19708⟩, x0, x1, x2, x3, ⟨64⟩]
  obtain ⟨_, _, _, r2⟩ := metaMorphoV1_1Creation_block_1251_packed (by simp) r1
  rw [he2.1, he2.2, constructorRuntimePart_compose] at r2
  have hp2 := hc.trans (constructorRuntimePart_prefix (constructorRuntimeCopy mem tail ptr) ptr w 0 21)
  have hm2 : 480 ≤ (constructorRuntimePart (constructorRuntimeCopy mem tail ptr) ptr w 0 21).size :=
    le_trans hm hp2.size
  have hr2 (off : Nat) (h1 : 128 ≤ off) (h2 : off + 32 ≤ 480) :
      memLoad (UInt256.ofNat off) (constructorRuntimePart (constructorRuntimeCopy mem tail ptr) ptr w 0 21) =
        w off :=
    hp2.load_preserved (by omega) (by omega) (by omega) (by omega)
  have hret := constructorRuntimeFinish (by simp) hm2 hlo hfit hr2 r2
  rw [constructorRuntimePart_compose, constructorRuntimePart_return] at hret
  exact hret

end Benchmarks.Morpho.MetaMorphoV1_1
