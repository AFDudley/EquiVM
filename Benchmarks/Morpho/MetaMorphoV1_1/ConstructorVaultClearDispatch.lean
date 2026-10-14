import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultClearLoop

/-! Dispatch to obsolete vault-string clearing only when an old long string shrinks. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

def constructorVaultShrinkPC (symbol : Bool) : UInt256 := if symbol then ⟨1744⟩ else ⟨2001⟩
def constructorVaultClearStartPC (symbol : Bool) : UInt256 := if symbol then ⟨1753⟩ else ⟨2010⟩

theorem constructorVaultClearDispatch {tail : ByteArray} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {old len : UInt256} {R : List UInt256}
    (symbol : Bool) (hstack : R.length + 4 ≤ 1024)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultOldPC symbol)
      (old :: len :: R) mem aw out σ k C) :
    ((old.toNat < 32 ∨ old.toNat ≤ len.toNat) ∧
      ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultStorePC symbol)
        (old :: len :: R) mem aw' out σ k' C') ∨
    (32 ≤ old.toNat ∧ len.toNat < old.toNat ∧
      ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultClearStartPC symbol)
        (old :: len :: R) mem aw' out σ k' C') := by
  by_cases hs : old.toNat < 32
  · refine .inl ⟨.inl hs, ?_⟩
    have hc : UInt256.gt old (UInt256.ofNat 31) = UInt256.ofNat 0 :=
      ult_zero (by change old.toNat ≤ 31; omega)
    cases symbol with
    | false =>
        exact metaMorphoV1_1Creation_block_805_fallthrough_packed
           (by simp only [List.length_cons]; omega) hc rd
    | true =>
        exact metaMorphoV1_1Creation_block_930_fallthrough_packed
           (by simp only [List.length_cons]; omega) hc rd
  · have hc : UInt256.gt old (UInt256.ofNat 31) ≠ UInt256.ofNat 0 := by
      rw [show UInt256.gt old (UInt256.ofNat 31) = ⟨1⟩ from
        ult_one (by change 31 < old.toNat; omega)]
      decide
    have hnext : ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultShrinkPC symbol)
        (old :: len :: R) mem aw' out σ k' C' := by
      cases symbol with
      | false =>
          exact metaMorphoV1_1Creation_block_805_taken_packed 
            (by simp only [List.length_cons]; omega) hc
            (by native_decide) rd
      | true =>
          exact metaMorphoV1_1Creation_block_930_taken_packed 
            (by simp only [List.length_cons]; omega) hc
            (by native_decide) rd
    obtain ⟨aw1, k1, C1, h1⟩ := hnext
    by_cases hg : old.toNat ≤ len.toNat
    · refine .inl ⟨.inr hg, ?_⟩
      have hcond : UInt256.isZero (UInt256.gt old len) ≠ UInt256.ofNat 0 := by
        change UInt256.isZero (UInt256.lt len old) ≠ ⟨0⟩
        rw [ult_zero hg]; decide
      cases symbol with
      | false =>
          exact metaMorphoV1_1Creation_block_2001_taken_packed 
            hstack hcond (by native_decide) h1
      | true =>
          exact metaMorphoV1_1Creation_block_1744_taken_packed 
            hstack hcond (by native_decide) h1
    · refine .inr ⟨by omega, by omega, ?_⟩
      have hcond : UInt256.isZero (UInt256.gt old len) = UInt256.ofNat 0 := by
        change UInt256.isZero (UInt256.lt len old) = ⟨0⟩
        rw [ult_one (by omega)]; decide
      cases symbol with
      | false =>
          exact metaMorphoV1_1Creation_block_2001_fallthrough_packed
             hstack hcond h1
      | true =>
          exact metaMorphoV1_1Creation_block_1744_fallthrough_packed
             hstack hcond h1

end Benchmarks.Morpho.MetaMorphoV1_1
