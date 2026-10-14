import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultHeader
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_007

/-! The vault metadata clearing loops preserve the source's forward write order. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

def constructorVaultClearLoopPC (symbol : Bool) : UInt256 := if symbol then ⟨1789⟩ else ⟨2046⟩

theorem constructorVaultClearLoopExit {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {i base count : UInt256} {R : List UInt256} (symbol : Bool)
    (hstack : R.length + 5 ≤ 1024) (hcond : UInt256.lt i count = ⟨0⟩)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultClearLoopPC symbol)
      (i :: base :: count :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorVaultStorePC symbol) (count :: R) mem aw' rdata σ k' C' := by
  cases symbol with
  | false =>
    obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_2046_fallthrough_packed hstack hcond rd
    exact metaMorphoV1_1Creation_block_2054_packed
      (by simp only [List.length_cons]; omega) (by native_decide) r1
  | true =>
    obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_1789_fallthrough_packed hstack hcond rd
    exact metaMorphoV1_1Creation_block_1797_packed
      (by simp only [List.length_cons]; omega) (by native_decide) r1

theorem constructorVaultClearLoopStep {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {i base count : UInt256} {R : List UInt256} (symbol : Bool)
    (hstack : R.length + 6 ≤ 1024) (hperm : I.perm = true)
    (hcond : UInt256.lt i count ≠ ⟨0⟩)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultClearLoopPC symbol)
      (i :: base :: count :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorVaultClearLoopPC symbol) ((UInt256.ofNat 1 + i) :: base :: count :: R)
      mem aw' rdata (sstoreAccountMap I.codeOwner σ (i + base) ⟨0⟩) k' C' := by
  cases symbol with
  | false =>
    obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_2046_taken_packed
      (by omega) hcond (by native_decide) rd
    exact metaMorphoV1_1Creation_block_2060_packed
      (by simp only [List.length_cons]; omega) hperm (by native_decide) r1
  | true =>
    obtain ⟨_, _, _, r1⟩ := metaMorphoV1_1Creation_block_1789_taken_packed
      (by omega) hcond (by native_decide) rd
    exact metaMorphoV1_1Creation_block_1803_packed
      (by simp only [List.length_cons]; omega) hperm (by native_decide) r1

theorem constructorVaultClearLoop {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {base first count : UInt256} {R : List UInt256} (symbol : Bool) (n i : Nat)
    (hstack : R.length + 6 ≤ 1024) (hperm : I.perm = true)
    (hcount : count.toNat = i + n)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultClearLoopPC symbol)
      (UInt256.ofNat i :: (base + first) :: count :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
      (constructorVaultStorePC symbol) (count :: R) mem aw' rdata
      (clearDataWordsForwardFrom I.codeOwner σ base (UInt256.ofNat i + first) n) k' C' := by
  have hb : count.toNat < UInt256.size := count.val.isLt
  induction n generalizing i σ aw k C with
  | zero =>
    exact constructorVaultClearLoopExit symbol (by omega)
      (ult_zero (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)) rd
  | succ n ih =>
    obtain ⟨_, _, _, r1⟩ := constructorVaultClearLoopStep symbol hstack hperm
      (by rw [ult_one (by rw [UInt256.toNat_ofNat_of_lt (by omega)]; omega)]; decide) rd
    rw [show UInt256.ofNat i + (base + first) = base + (UInt256.ofNat i + first) by
      rw [← u256_add_assoc, u256_add_comm (UInt256.ofNat i) base, u256_add_assoc]] at r1
    simp only [show UInt256.ofNat 1 = (⟨1⟩ : UInt256) from rfl, u256_one_add_ofNat] at r1
    obtain ⟨aw2, k2, C2, r2⟩ := ih (i + 1) (by omega) r1
    refine ⟨aw2, k2, C2, ?_⟩
    have hi : (⟨1⟩ : UInt256) + (UInt256.ofNat i + first) =
        UInt256.ofNat (i + 1) + first := by
      rw [← u256_add_assoc, u256_one_add_ofNat]
    simpa only [clearDataWordsForwardFrom, hi] using r2

end Benchmarks.Morpho.MetaMorphoV1_1
