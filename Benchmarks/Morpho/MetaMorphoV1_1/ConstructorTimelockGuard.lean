import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorOwnershipRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.TimelockBoundsSource

/-! The constructor accepts zero timelock or the shared nonzero timelock range. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

def constructorTimelockValid (value : UInt256) : Prop := value = ⟨0⟩ ∨ timelockInBounds value

theorem constructorTimelockGuard {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {value : UInt256} {R : List UInt256} (hstack : R.length + 3 ≤ 1024)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨711⟩ (value :: R)
      mem aw rdata σ k C) :
    (¬ constructorTimelockValid value ∧ RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    (constructorTimelockValid value ∧ ∃ aw' k' C',
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨716⟩ (value :: R)
        mem aw' rdata σ k' C') := by
  by_cases hz : value = ⟨0⟩
  · exact .inr ⟨.inl hz, metaMorphoV1_1Creation_block_711_fallthrough_packed hstack hz rd⟩
  · have r1 := metaMorphoV1_1Creation_block_711_taken hstack hz (by native_decide) rd
    by_cases hhi : value.toNat ≤ 1209600
    · have r2 := metaMorphoV1_1Creation_block_2091_fallthrough hstack (ugt_zero hhi) r1
      by_cases hlo : 86400 ≤ value.toNat
      · have hl : UInt256.lt value (UInt256.ofNat 86400) = ⟨0⟩ := ult_zero hlo
        exact .inr ⟨.inr ⟨hhi, hlo⟩, metaMorphoV1_1Creation_block_2102_taken_packed
          hstack (by rw [hl]; decide) (by native_decide) r2⟩
      · have hl : UInt256.lt value (UInt256.ofNat 86400) = ⟨1⟩ := ult_one (Nat.lt_of_not_ge hlo)
        have r3 := metaMorphoV1_1Creation_block_2102_fallthrough hstack
          (by rw [hl]; rfl) r2
        refine .inl ⟨?_, metaMorphoV1_1Creation_block_2113
          (by simp only [List.length_cons]; omega) r3⟩
        rintro (hzero | hbound)
        · exact hz hzero
        · exact hlo hbound.2
    · have hh : UInt256.gt value (UInt256.ofNat 1209600) = ⟨1⟩ := ugt_one (Nat.lt_of_not_ge hhi)
      have r2 := metaMorphoV1_1Creation_block_2091_taken hstack
        (by rw [hh]; decide) (by native_decide) r1
      refine .inl ⟨?_, metaMorphoV1_1Creation_block_2127
        (by simp only [List.length_cons]; omega) r2⟩
      rintro (hzero | hbound)
      · exact hz hzero
      · exact hhi hbound.1

end Benchmarks.Morpho.MetaMorphoV1_1
