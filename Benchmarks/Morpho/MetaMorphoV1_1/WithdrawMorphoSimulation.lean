import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawMorphoLoop
import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawMorphoFunctionSource

/-! Complete simulation of the allocated mutating market-withdrawal helper. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem withdrawMorphoSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr assets ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 28 ≤ 1024)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hhi : ptr.toNat < 2 ^ 64)
    (hmem : 96 ≤ mem.size) (hs : SourceState s0 I σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨18661⟩ (assets :: ret :: R) mem aw rdata σ k C) :
    (ExecFuncBody config (allocatedWithdrawMorphoFrame (immStore v) assets ptr) evm
        allocatedWithdrawMorphoFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (cursor : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      ExecFuncBody config (allocatedWithdrawMorphoFrame (immStore v) assets ptr) evm
        allocatedWithdrawMorphoFunction.body (.returned frame' evm' (some [.tuple [], uint256Value cursor])) ∧
      memLoad ⟨64⟩ mem' = cursor ∧ cursor.toNat < 2 ^ 64 ∧ ptr.toNat ≤ cursor.toNat ∧
      MemoryPrefix mem mem' ptr.toNat ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R mem' aw' out evm'.accountMap k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_18661_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) rd
  rcases withdrawMorphoLoopSimulation v UInt256.size hstack (withdrawMorphoInitialLocals v assets ptr)
      hcalldata hfree hlo hhi hmem hs (by rfl) hret h1 with
    ⟨hbad, hrev⟩ | ⟨evm', frame', index, assets', cursor, mem', out,
      hs', hl', hfree', hhi', hmono, hprefix, hresult⟩
  · refine .inl ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    apply (withdrawMorphoFunctionPrefix v evm assets ptr).run
    rw [allocatedWithdrawMorphoFunction_body]
    exact ExecBlock.consRevert (withdrawMorphoForSource hbad)
  · rcases hresult with ⟨hreturn, hdone⟩ | ⟨hexit, aw2, k2, C2, h2⟩
    · refine .inr ⟨evm', frame', cursor, mem', out, hs', ExecFuncBody.execBlockRet ?_,
        hfree', hhi', hmono, hprefix, hdone⟩
      apply (withdrawMorphoFunctionPrefix v evm assets ptr).run
      rw [allocatedWithdrawMorphoFunction_body]
      exact ExecBlock.consReturn (withdrawMorphoForSource hreturn)
    · have htest := supplyMorphoDoneCondition (evm := evm') hl'.assets
      by_cases hz : assets' = ⟨0⟩
      · rw [decide_eq_true hz] at htest
        obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_18945_fallthrough_packed
          (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega) hz h2
        obtain ⟨aw4, k4, C4, h4⟩ := metaMorphoV1_1_block_18951_packed
          (immWords := wordsOf (immStore v)) (by simp only [List.append]; omega) hret h3
        refine .inr ⟨evm', frame', cursor, mem', out, hs', ExecFuncBody.execBlockRet ?_,
          hfree', hhi', hmono, hprefix, aw4, k4, C4, h4⟩
        apply (withdrawMorphoFunctionPrefix v evm assets ptr).run
        rw [allocatedWithdrawMorphoFunction_body]
        exact ExecBlock.consNormal (withdrawMorphoForSource hexit)
          (ExecBlock.consNormal (ExecStmt.requireTrue htest)
            (ExecBlock.consReturn (supplyMorphoReturnSource hl'.cursor)))
      · rw [decide_eq_false hz] at htest
        obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_18945_taken_packed
          (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega) hz
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
        refine .inl ⟨ExecFuncBody.execBlockRevert ?_, metaMorphoV1_1_block_18952
          (immWords := wordsOf (immStore v)) (by simp only [metaMorphoV1_1_block_18945_taken_stack, List.append, List.length_cons]; omega) h3⟩
        apply (withdrawMorphoFunctionPrefix v evm assets ptr).run
        rw [allocatedWithdrawMorphoFunction_body]
        exact ExecBlock.consNormal (withdrawMorphoForSource hexit)
          (ExecBlock.consRevert (ExecStmt.requireFalse htest))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
