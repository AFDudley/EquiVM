import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoIteration

/-! Supply-loop induction over the remaining word-sized index range. The queue length is
read again after every call, so this proof permits arbitrary callee storage changes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem supplyMorphoLoopSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr assets ret i : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (remaining : Nat) (hstack : R.length + 25 ≤ 1024)
    (hl : SupplyLoopLocals v frame i assets ptr)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hhi : ptr.toNat < 2 ^ 64)
    (hmem : 96 ≤ mem.size) (hs : SourceState s0 I σ evm)
    (hdiff : UInt256.size = i.toNat + remaining)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨17937⟩
      ([i, UInt256.ofNat v.MORPHO.toNat, assets, UInt256.ofNat v.MORPHO.toNat, ret] ++ R)
      mem aw rdata σ k C) :
    (ExecForLoop config frame evm maxDepositCondition maxDepositPost supplyMorphoIteration .reverted ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (index assets' cursor : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧ SupplyLoopLocals v frame' index assets' cursor ∧
      memLoad ⟨64⟩ mem' = cursor ∧ cursor.toNat < 2 ^ 64 ∧ ptr.toNat ≤ cursor.toNat ∧
      MemoryPrefix mem mem' ptr.toNat ∧
      ((ExecForLoop config frame evm maxDepositCondition maxDepositPost supplyMorphoIteration
          (.returned frame' evm' (some [.tuple [], uint256Value cursor])) ∧
        ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R mem' aw' out evm'.accountMap k' C') ∨
       (ExecForLoop config frame evm maxDepositCondition maxDepositPost supplyMorphoIteration
          (.ok frame' evm') ∧
        ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨18353⟩
          ([index, UInt256.ofNat v.MORPHO.toNat, assets', UInt256.ofNat v.MORPHO.toNat, ret] ++ R)
          mem' aw' out evm'.accountMap k' C')) := by
  induction remaining generalizing evm frame mem aw rdata σ k C ptr assets i with
  | zero =>
      have hi : i.toNat < UInt256.size := i.val.isLt
      omega
  | succ n ih =>
      let len := codeOwnerStorageWord I σ ⟨20⟩
      have htest := maxDepositConditionSource hl.contract hl.queue hl.index (hs.storageRead ⟨20⟩)
      by_cases hlt : i.toNat < len.toNat
      · rw [decide_eq_true hlt] at htest
        obtain ⟨k1, C1, h1⟩ := metaMorphoV1_1_block_17937_fallthrough
          (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
          (by change UInt256.isZero (UInt256.lt i len) = ⟨0⟩; rw [ult_one hlt]; decide) rd
        rcases supplyMorphoIterationSimulation v hstack hl hcalldata hfree hlo hhi hmem hs hlt hret h1 with
          ⟨hbad, hrev⟩ | ⟨evm2, frame2, assets2, ptr2, mem2, out2,
            hs2, hl2, hfree2, hhi2, hmono2, hprefix2, hbody⟩
        · exact .inl ⟨ExecForLoop.bodyRevert htest hbad, hrev⟩
        rcases hbody with ⟨hreturn, hdone⟩ | ⟨hnext, aw2, k2, C2, h2⟩
        · exact .inr ⟨evm2, frame2, i, assets2, ptr2, mem2, out2, hs2, hl2,
            hfree2, hhi2, hmono2, hprefix2, .inl ⟨ExecForLoop.bodyReturn htest hreturn, hdone⟩⟩
        · have hfit : i.toNat + 1 < UInt256.size := by
            have hlen : len.toNat < UInt256.size := len.val.isLt
            omega
          have hpost := maxDepositPostSource (evm := evm2) hl2.index hfit
          have hstep {result : ExecResult}
              (hloop : ExecForLoop config (maxDepositPostFrame frame2 i) evm2
                maxDepositCondition maxDepositPost supplyMorphoIteration result) :
              ExecForLoop config frame evm maxDepositCondition maxDepositPost supplyMorphoIteration result := by
            rcases hnext with hnext | hnext
            · exact ExecForLoop.iterate htest hnext hpost hloop
            · exact ExecForLoop.continueIter htest hnext hpost hloop
          obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_18180_packed
            (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
            (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
          have hdiff2 : UInt256.size = (i + ⟨1⟩).toNat + n := by
            have hadd : (i + ⟨1⟩).toNat = i.toNat + 1 := addWord_toNat i ⟨1⟩ hfit
            rw [hadd]
            omega
          rcases ih hl2.post hfree2 (by omega) hhi2 (le_trans hmem hprefix2.size) hs2 hdiff2 h3 with
            ⟨hbad, hrev⟩ | ⟨evm3, frame3, index3, assets3, cursor3, mem3, out3,
              hs3, hl3, hfree3, hhi3, hmono3, hprefix3, hresult⟩
          · exact .inl ⟨hstep hbad, hrev⟩
          · refine .inr ⟨evm3, frame3, index3, assets3, cursor3, mem3, out3, hs3, hl3,
              hfree3, hhi3, le_trans hmono2 hmono3,
              hprefix2.trans (hprefix3.mono hmono2), ?_⟩
            rcases hresult with ⟨hreturn, hdone⟩ | ⟨hexit, hdone⟩
            · exact .inl ⟨hstep hreturn, hdone⟩
            · exact .inr ⟨hstep hexit, hdone⟩
      · rw [decide_eq_false hlt] at htest
        obtain ⟨k1, C1, h1⟩ := metaMorphoV1_1_block_17937_taken
          (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
          (by change UInt256.isZero (UInt256.lt i len) ≠ ⟨0⟩
              rw [ult_zero (Nat.le_of_not_gt hlt)]; decide)
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
        rw [hs.accounts] at h1
        exact .inr ⟨evm, frame, i, assets, ptr, mem, rdata, ⟨hs.world, hs.env, rfl⟩, hl,
          hfree, hhi, le_refl _, .refl _ _, .inr ⟨ExecForLoop.falseDone htest, aw, k1, C1, h1⟩⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
