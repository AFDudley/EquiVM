import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateIteration
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateLoopData
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_031

/-! Inductive simulation of the reallocation loop, retaining the actual state of every call. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem reallocateLoopSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {values : List Value} {mem rdata : ByteArray} {aw : UInt256} {k C : Nat}
    {ptr withdrawn offset i len supplied saved : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (remaining : Nat) (hstack : R.length + 29 ≤ 1024)
    (hd : ReallocateLoopData I.calldata values offset len)
    (hl : ReallocateLocals v frame values i supplied withdrawn ptr)
    (hdiff : len.toNat = i.toNat + remaining)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hs : SourceState s0 I evm.accountMap evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨5954⟩
      ([withdrawn, offset, i, len, supplied, saved] ++ R) mem aw rdata evm.accountMap k C) :
    (ExecForLoop config frame evm reallocateCondition reallocatePost reallocateIteration .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    (ExecForLoop config frame evm reallocateCondition reallocatePost reallocateIteration .staticViolation ∧
      RDstatic (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (mem' out : ByteArray)
      (aw' supplied' withdrawn' ptr' : UInt256) (k' C' : Nat),
      SourceState s0 I evm'.accountMap evm' ∧ ReallocateLocals v frame' values len supplied' withdrawn' ptr' ∧
      ExecForLoop config frame evm reallocateCondition reallocatePost reallocateIteration (.ok frame' evm') ∧
      RD (deployedRuntime v) I g s0 ⟨6789⟩
        ([withdrawn', offset, len, len, supplied', saved] ++ R) mem' aw' out evm'.accountMap k' C' := by
  induction remaining generalizing evm frame mem rdata aw ptr withdrawn supplied i k C with
  | zero =>
      have he : i = len := u256_inj (by omega)
      subst i
      have hcond := reallocateConditionSource (evm := evm) hl
      rw [hd.count, decide_eq_false (Nat.lt_irrefl _)] at hcond
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_5954_taken_packed
        (immWords := wordsOf (immStore v)) (by dsimp only [List.append, List.length_cons]; omega)
        (by rw [ult_zero (le_refl _)]; decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
      exact .inr (.inr ⟨evm, frame, mem, rdata, aw1, supplied, withdrawn, ptr, k1, C1,
        hs, hl, ExecForLoop.falseDone hcond, h1⟩)
  | succ n ih =>
      have hi : i.toNat < len.toNat := by omega
      have hcond := reallocateConditionSource (evm := evm) hl
      rw [hd.count, decide_eq_true hi] at hcond
      obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_5954_fallthrough_packed
        (immWords := wordsOf (immStore v)) (by dsimp only [List.append, List.length_cons]; omega)
        (by rw [ult_one hi]; rfl) rd
      have hb := hd.rowBounds hi
      have hsafe : UInt256.slt (reallocateRemaining I.calldata offset i) (UInt256.ofNat 192) = ⟨0⟩ :=
        slt_lit_zero (by decide) hb.2.1 hb.2.2
      obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_5963_fallthrough_packed
        (immWords := wordsOf (immStore v)) (by dsimp only [List.append, List.length_cons]; omega) hsafe h1
      have hcalldata : I.calldata.size < UInt256.size := lt_trans hd.high (by decide)
      rcases reallocateIterationSimulation v hstack hl (hd.rows i hi) hb.1
          (lt_of_le_of_lt hb.1 hcalldata) hcalldata hfree hlo (by omega) hb.2.2 hs h2 with
        ⟨hbad, hrev⟩ | ⟨hstatic, hsrev⟩ |
          ⟨evm3, frame3, mem3, out3, aw3, supplied3, withdrawn3, ptr3, k3, C3,
            hs3, hl3, hbody, hf3, hlo3, _, _, h3⟩
      · exact .inl ⟨ExecForLoop.bodyRevert hcond hbad, hrev⟩
      · exact .inr (.inl ⟨ExecForLoop.bodyStatic hcond hstatic, hsrev⟩)
      · have hn : len.toNat < UInt256.size := len.val.isLt
        have hfit : i.toNat + 1 < UInt256.size := by omega
        have hinc : (i + (⟨1⟩ : UInt256)).toNat = i.toNat + 1 := addWord_toNat i ⟨1⟩ hfit
        have hpost := reallocatePostSource (evm := evm3) hl3 hfit
        let frame4 : Frame := { frame3 with locals := frame3.locals.insert "i" (uint256Value (i + ⟨1⟩)) }
        have hl4 : ReallocateLocals v frame4 values (i + ⟨1⟩) supplied3 withdrawn3 ptr3 := hl3.withIndex _
        obtain ⟨aw4, k4, C4, h4⟩ := metaMorphoV1_1_block_6380_packed
          (immWords := wordsOf (immStore v)) (by dsimp only [List.append, List.length_cons]; omega)
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
        have wrap {result : ExecResult}
            (hloop : ExecForLoop config frame4 evm3 reallocateCondition reallocatePost reallocateIteration result) :
            ExecForLoop config frame evm reallocateCondition reallocatePost reallocateIteration result :=
          hbody.elim (fun h ↦ ExecForLoop.iterate hcond h hpost hloop)
            (fun h ↦ ExecForLoop.continueIter hcond h hpost hloop)
        rcases ih hl4 (by omega) hf3 hlo3 hs3 h4 with
          ⟨hbad, hrev⟩ | ⟨hstatic, hsrev⟩ |
            ⟨evm5, frame5, mem5, out5, aw5, supplied5, withdrawn5, ptr5, k5, C5,
              hs5, hl5, hloop, h5⟩
        · exact .inl ⟨wrap hbad, hrev⟩
        · exact .inr (.inl ⟨wrap hstatic, hsrev⟩)
        · exact .inr (.inr ⟨evm5, frame5, mem5, out5, aw5, supplied5, withdrawn5, ptr5, k5, C5,
            hs5, hl5, wrap hloop, h5⟩)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
