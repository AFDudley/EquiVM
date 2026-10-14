import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoExternalSource
import Benchmarks.Morpho.MetaMorphoV1_1.MorphoAccrueCall
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_009

/-! The supply loop's code guard and interest-accrual call, including their source execution. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem supplyMorphoAccrualSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params id cap i : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 13 ≤ 1024)
    (himms : frame.immutables = immStore v)
    (hm : frame.locals.get? "morphoTarget" = some (.address v.MORPHO))
    (hp : frame.locals.get? "marketParams" = some p.value)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hptr : ptr.toNat < 2 ^ 64)
    (hparamslo : 96 ≤ params.toNat) (hparams : params.toNat + 160 ≤ ptr.toNat)
    (hmem : params.toNat + 160 ≤ mem.size) (hloads : MarketParamsLoads mem params p)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨18003⟩
      (params :: cap :: id :: i :: UInt256.ofNat v.MORPHO.toNat :: R) mem aw rdata σ k C) :
    ((∀ tail, ExecBlock config frame evm (supplyMorphoAccrual ++ tail) .reverted) ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      SourceState s0 I evm'.accountMap evm' ∧
      (∀ tail result, ExecBlock config (supplyAccruedFrame frame) evm' tail result →
        ExecBlock config frame evm (supplyMorphoAccrual ++ tail) result) ∧
      RD (deployedRuntime v) I g s0 ⟨18057⟩
        (⟨0⟩ :: id :: cap :: params :: i :: UInt256.ofNat v.MORPHO.toNat :: R)
        (morphoAccrueReturnMem mem ptr p) aw' out evm'.accountMap k' C' := by
  have hcode := supplyMorphoCodeSource (evm := evm) v himms
  have ha : AccountAddress.ofUInt256 (UInt256.ofNat v.MORPHO.toNat) = v.MORPHO := by
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    exact accountAddress_of_word_val _
  by_cases hz : extCodeSizeWord σ (UInt256.ofNat v.MORPHO.toNat) = ⟨0⟩
  · obtain ⟨k1, C1, h1⟩ := metaMorphoV1_1_block_18003_taken
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [hz]; decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    refine .inl ⟨fun _ ↦ ExecBlock.consRevert (ExecStmt.requireFalse ?_),
      metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_18003_taken_stack, List.length_cons]; omega) h1⟩
    simpa only [← hs.accounts, hz, ne_eq, not_true_eq_false, decide_false] using hcode
  · have hguard : ExecStmt config frame evm supplyMorphoAccrual[0]! (.ok frame evm) :=
      ExecStmt.requireTrue (by
        rw [← hs.accounts] at hcode
        rw [decide_eq_true hz] at hcode
        exact hcode)
    obtain ⟨k1, C1, h1⟩ := metaMorphoV1_1_block_18003_fallthrough
      (immWords := wordsOf (immStore v)) (by omega) (isZero_eq_zero_of_ne hz) rd
    obtain ⟨gasArg, aw2, k2, C2, h2⟩ := morphoAccrueReachCall v p hstack
      hfree hptr hparamslo hparams hmem hloads h1
    rcases morphoAccrueCallSimulation v p (UInt256.ofNat v.MORPHO.toNat)
        (by simp only [List.length_cons]; omega) hs hptr h2 with
      ⟨evm', out, hcall, hrev⟩ | ⟨evm', out, aw3, k3, C3, hcall, hs', h3⟩
    · rw [ha] at hcall
      exact .inl ⟨fun _ ↦ ExecBlock.consNormal hguard
        (ExecBlock.consRevert (supplyAccrueSourceReverts hm hp hcall)), hrev⟩
    · rw [ha] at hcall
      exact .inr ⟨evm', out, aw3, k3, C3, hs', fun _ _ htail ↦
        ExecBlock.consNormal hguard
          (ExecBlock.consNormal (supplyAccrueSourceReturns hm hp hcall) htail), h3⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
