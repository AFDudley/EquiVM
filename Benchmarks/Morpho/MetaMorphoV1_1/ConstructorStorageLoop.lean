import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStorageHeader
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_011

/-! The creation-code loops clear obsolete string data in forward slot order. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

def constructorStorageLoopPC (symbol : Bool) : UInt256 := if symbol then ⟨2348⟩ else ⟨2560⟩
def constructorStorageWritePC (symbol : Bool) : UInt256 := if symbol then ⟨392⟩ else ⟨296⟩

theorem constructorStorageLoopExit {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {i base count : UInt256} {R : List UInt256} (symbol : Bool)
    (hstack : R.length + 5 ≤ 1024) (hcond : UInt256.lt i count = ⟨0⟩)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorStorageLoopPC symbol)
      (i :: base :: count :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorStorageWritePC symbol) (count :: R) mem aw' rdata σ k' C' := by
  cases symbol with
  | false =>
    obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_2560_fallthrough_packed hstack hcond rd
    exact metaMorphoV1_1Creation_block_2568_packed
      (by simp only [List.length_cons]; omega) (by native_decide) r1
  | true =>
    obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_2348_fallthrough_packed hstack hcond rd
    exact metaMorphoV1_1Creation_block_2356_packed
      (by simp only [List.length_cons]; omega) (by native_decide) r1

theorem constructorStorageLoopStep {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {i base count ptr len : UInt256} {R : List UInt256} (symbol : Bool)
    (hstack : R.length + 9 ≤ 1024) (hperm : I.perm = true)
    (hcond : UInt256.lt i count ≠ ⟨0⟩)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorStorageLoopPC symbol)
      (i :: base :: count :: ptr :: len :: len :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorStorageLoopPC symbol)
      ((UInt256.ofNat 1 + i) :: base :: count :: ptr :: len :: len :: R) mem aw' rdata
      (sstoreAccountMap I.codeOwner σ (base + i) ⟨0⟩) k' C' := by
  cases symbol with
  | false =>
    obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_2560_taken_packed
      (by simp only [List.length_cons]; omega) hcond (by native_decide) rd
    exact metaMorphoV1_1Creation_block_2574_packed hstack hperm (by native_decide) r1
  | true =>
    obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_2348_taken_packed
      (by simp only [List.length_cons]; omega) hcond (by native_decide) rd
    exact metaMorphoV1_1Creation_block_2362_packed hstack hperm (by native_decide) r1

theorem constructorStorageLoop {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {base count ptr len : UInt256} {R : List UInt256} (symbol : Bool) (n i : Nat)
    (hstack : R.length + 9 ≤ 1024) (hperm : I.perm = true)
    (hcount : count.toNat = i + n)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorStorageLoopPC symbol)
      (UInt256.ofNat i :: base :: count :: ptr :: len :: len :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorStorageWritePC symbol) (count :: ptr :: len :: len :: R) mem aw' rdata
      (clearDataWordsForwardFrom I.codeOwner σ base (UInt256.ofNat i) n) k' C' := by
  have hb : count.toNat < UInt256.size := count.val.isLt
  induction n generalizing i σ aw k C with
  | zero =>
    exact constructorStorageLoopExit symbol (by simp only [List.length_cons]; omega)
      (ult_zero (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)) rd
  | succ n ih =>
    obtain ⟨_, _, _, r1⟩ := constructorStorageLoopStep symbol hstack hperm
      (by rw [ult_one (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)]; decide) rd
    simp only [show UInt256.ofNat 1 = (⟨1⟩ : UInt256) from rfl, u256_one_add_ofNat] at r1
    obtain ⟨aw2, k2, C2, r2⟩ := ih (i + 1) (by omega) r1
    exact ⟨aw2, k2, C2, by simpa only [clearDataWordsForwardFrom, u256_one_add_ofNat] using r2⟩

end Benchmarks.Morpho.MetaMorphoV1_1
