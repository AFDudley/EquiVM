import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateCalldataChecks
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateRole
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateLoop
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocatePublicSource
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateFinishRuntime

/-! Compose authorization, all allocation rows, and conservation for public reallocation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem reallocateSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem out : ByteArray} {aw saved : UInt256} {k C : Nat} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 29 ≤ 1024)
    (hc : ReallocateCalldataChecks I.calldata) (hs : SourceState s0 I evm.accountMap evm)
    (hwv : I.weiValue = ⟨0⟩) (hmem : 96 ≤ mem.size) (hfree : memLoad ⟨64⟩ mem = ⟨128⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨5916⟩
      (reallocateCount I.calldata :: calldataWord I.calldata 4 :: saved :: R)
      mem aw out evm.accountMap k C) :
    (ExecTransitionBody config contract evm (reallocateCalldataLocals I.calldata)
      allocatedReallocateTransition.body .reverted (immStore v) ∧ RDrev (deployedRuntime v) g s0) ∨
    (ExecTransitionBody config contract evm (reallocateCalldataLocals I.calldata)
      allocatedReallocateTransition.body .staticViolation (immStore v) ∧ RDstatic (deployedRuntime v) g s0) ∨
    ∃ (frame : Frame) (evm' : State),
      ExecTransitionBody config contract evm (reallocateCalldataLocals I.calldata)
        allocatedReallocateTransition.body (.returned frame evm' none) (immStore v) ∧
      RDret (deployedRuntime v) g s0 evm'.accountMap ByteArray.empty := by
  have hwv' : evm.executionEnv.weiValue = ⟨0⟩ := by rw [hs.env]; exact hwv
  have hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4 := by
    rw [hs.env]; have := hc.high; omega
  have rdenv : RD (deployedRuntime v) evm.executionEnv g s0 ⟨5916⟩
      (reallocateCount I.calldata :: calldataWord I.calldata 4 :: saved :: R)
      mem aw out evm.accountMap k C := by rw [hs.env]; exact rd
  rcases reallocateRole (evm := evm) v (by simp only [List.length_cons]; omega) rdenv with
    ⟨hrole, hrev⟩ | ⟨hrole, aw1, k1, C1, r1⟩
  · exact .inl ⟨reallocateRoleRevertsSource evm v (reallocateInput I.calldata) hwv' hhi hrole, hrev⟩
  rw [hs.env] at r1
  have hp := reallocatePublicPrefix evm v (reallocateInput I.calldata) hwv' hhi hrole
  have hl := reallocateInitialLocals evm v (reallocateInput I.calldata)
  have hf : memLoad ⟨64⟩
      (twoWordHashMem (UInt256.ofNat evm.executionEnv.source.val) ⟨11⟩ mem) = ⟨128⟩ :=
    (twoWordHashMem_free _ _ hmem).trans hfree
  rw [hs.env] at hf
  have r2 := metaMorphoV1_1_block_5949 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) r1
  have hdiff : (reallocateCount I.calldata).toNat = (⟨0⟩ : UInt256).toNat +
      (reallocateCount I.calldata).toNat := (Nat.zero_add _).symm
  rcases reallocateLoopSimulation (I := I) (g := g) (s0 := s0) (evm := evm)
      (i := ⟨0⟩) (supplied := ⟨0⟩) (withdrawn := ⟨0⟩) (saved := saved) (R := R)
      v (reallocateCount I.calldata).toNat hstack hc.loopData hl hdiff hf (by decide) hs r2 with
    ⟨hloop, hrev⟩ | ⟨hloop, hstatic⟩ |
      ⟨evm3, frame3, mem3, out3, aw3, supplied3, withdrawn3, ptr3, k3, C3,
        hs3, hl3, hloop, r3⟩
  · exact .inl ⟨ExecFuncBody.execBlockRevert (hp.run
      (ExecBlock.consRevert (ExecStmt.for (reallocateForInit _ _) hloop))), hrev⟩
  · exact .inr (.inl ⟨ExecFuncBody.execBlockStatic (hp.run
      (ExecBlock.consStatic (ExecStmt.for (reallocateForInit _ _) hloop))), hstatic⟩)
  · have hcheck := reallocateFinalCheckSource (evm := evm3) hl3.supplied hl3.withdrawn
    rcases reallocateFinish v (by omega) r3 with ⟨hne, hrev⟩ | ⟨he, hret⟩
    · rw [decide_eq_false hne] at hcheck
      exact .inl ⟨ExecFuncBody.execBlockRevert (hp.run
        (ExecBlock.consNormal (ExecStmt.for (reallocateForInit _ _) hloop)
          (ExecBlock.consRevert (ExecStmt.requireFalse hcheck)))), hrev⟩
    · rw [decide_eq_true he] at hcheck
      exact .inr (.inr ⟨frame3, evm3, ExecFuncBody.execBlockOK (hp.run
        (ExecBlock.consNormal (ExecStmt.for (reallocateForInit _ _) hloop)
          (ExecBlock.consNormal (ExecStmt.requireTrue hcheck) ExecBlock.nil))), hret⟩)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
