import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoQueue
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoReadersSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoArithmeticSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoAttempt
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoTail
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_082

/-! A complete supply iteration: skip an inactive market, return after supplying all assets,
or advance to the next market with the actual state and remaining assets. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem supplyMorphoIterationSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr assets ret i : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 25 ≤ 1024)
    (hl : SupplyLoopLocals v frame i assets ptr)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hhi : ptr.toNat < 2 ^ 64)
    (hmem : 96 ≤ mem.size) (hs : SourceState s0 I σ evm)
    (hbound : i.toNat < (codeOwnerStorageWord I σ ⟨20⟩).toNat)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨17948⟩
      ([i, UInt256.ofNat v.MORPHO.toNat, assets, UInt256.ofNat v.MORPHO.toNat, ret] ++ R)
      mem aw rdata σ k C) :
    (ExecBlock config frame evm supplyMorphoIteration .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (assets' cursor : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧ SupplyLoopLocals v frame' i assets' cursor ∧
      memLoad ⟨64⟩ mem' = cursor ∧ cursor.toNat < 2 ^ 64 ∧ ptr.toNat ≤ cursor.toNat ∧
      MemoryPrefix mem mem' ptr.toNat ∧
      ((ExecBlock config frame evm supplyMorphoIteration
          (.returned frame' evm' (some [.tuple [], uint256Value cursor])) ∧
        ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R mem' aw' out evm'.accountMap k' C') ∨
       ((ExecBlock config frame evm supplyMorphoIteration (.ok frame' evm') ∨
         ExecBlock config frame evm supplyMorphoIteration (.continue frame' evm')) ∧
        ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨18180⟩
          ([i, ⟨1⟩, UInt256.ofNat v.MORPHO.toNat, assets', UInt256.ofNat v.MORPHO.toNat, ret] ++ R)
          mem' aw' out evm'.accountMap k' C')) := by
  let id := maxDepositIdWord I σ i
  let cap := maxDepositCapWord I σ id
  let frame1 := maxDepositCapFrame frame id cap
  let mem1 := maxDepositQueueMemory mem id
  have hsource1 := supplyMorphoQueuePrefix hl.contract hl.queue hl.config hl.index hs hbound
  have hl1 : SupplyLoopLocals v frame1 i assets ptr := hl.cap id cap
  have hcap : frame1.locals.get? "supplyCap" = some (uint256Value cap) := store_get_self _ _ _
  have hfree1 : memLoad ⟨64⟩ mem1 = ptr := by rw [maxDepositQueueMemory_free id hmem, hfree]
  have hprefix1 : MemoryPrefix mem mem1 ptr.toNat := maxDepositQueueMemory_prefix _ _ _
  obtain ⟨aw1, k1, C1, h1⟩ := supplyMorphoQueueRoutine v (by omega) hbound rd
  by_cases hz : cap = ⟨0⟩
  · rw [if_pos hz] at h1
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_18343_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    change RD (deployedRuntime v) I g s0 ⟨18180⟩
      ([i, ⟨1⟩, UInt256.ofNat v.MORPHO.toNat, assets, UInt256.ofNat v.MORPHO.toNat, ret] ++ R)
      mem1 aw2 rdata σ k2 C2 at h2
    rw [hs.accounts] at h2
    refine .inr ⟨evm, frame1, assets, ptr, mem1, rdata, ⟨hs.world, hs.env, rfl⟩,
      hl1, hfree1, hhi, le_refl _, hprefix1, .inr ⟨.inr ?_, aw2, k2, C2, h2⟩⟩
    apply hsource1.run
    apply ExecBlock.consContinue (ExecStmt.iteTrue ?_ (ExecBlock.consContinue ExecStmt.continue))
    rw [maxDepositCapConditionSource hcap, decide_eq_true hz]
  · rw [if_neg hz] at h1
    have hskip : ExecStmt config frame1 evm (.ite maxDepositCapCondition [.continue] [])
        (.ok frame1 evm) :=
      ExecStmt.iteFalse (by rw [maxDepositCapConditionSource hcap, decide_eq_false hz]) ExecBlock.nil
    have hid : frame1.locals.get? "id" = some (wordBytes32Value id) := by
      rw [show frame1 = maxDepositCapFrame frame id cap from rfl, maxDepositCapFrame,
        store_get_ne _ _ (by decide), store_get_self]
    obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_17995_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    rcases supplyMorphoReadersSimulation (frame := frame1) v
        (by simp only [List.append, List.length_cons]; omega) hl1.contract hl1.imms hl1.target hid
        hl1.cursor hcalldata hfree1 hlo hs h2 with
      ⟨hbad, hrev⟩ | ⟨evm2, params, market, mem2, out2, src, ptr1, shares, ptr2,
        hs2, hc2, hsource2, hfree2, hlo2, hhi2, hmem2, hmono2, hprefix2,
        hsrc, hspan, hloads, hsa, hss, aw3, k3, C3, h3⟩
    · exact .inl ⟨hsource1.run (ExecBlock.consNormal hskip (hbad _)), hrev⟩
    let frame2 := supplyMorphoReadersFrame frame1 params ptr1 market shares ptr2
    have hl2 : SupplyLoopLocals v frame2 i assets ptr2 := hl1.readers _ _ _ _ _
    have hcap2 : frame2.locals.get? "supplyCap" = some (uint256Value cap) := by
      rw [supplyMorphoReadersFrame_preserves _ _ _ _ _ _ _
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact hcap
    rcases supplyMorphoArithmeticSimulation (frame := frame2) v
        (by simp only [List.append, List.length_cons]; omega) hl2.contract
        (supplyMorphoReadersFrame_shares _ _ _ _ _ _) (supplyMorphoReadersFrame_market _ _ _ _ _ _)
        hcap2 hl2.assets hc2 hsa hss h3 with
      ⟨hbad, hrev⟩ | ⟨harith, aw4, k4, C4, h4⟩
    · exact .inl ⟨hsource1.run (ExecBlock.consNormal hskip
        (hsource2 _ _ (execBlock_reverted_append hbad))), hrev⟩
    let frame3 := supplyMorphoArithmeticFrame frame2 shares (calldataWord market 0)
      (calldataWord market 32) cap assets
    have hl3 : SupplyLoopLocals v frame3 i assets ptr2 := hl2.arithmetic _ _ _ _
    have hp3 : frame3.locals.get? "marketParams" = some (marketParamsData params).value := by
      rw [supplyMorphoArithmeticFrame_preserves _ _ _ _ _ _ _ (by decide) (by decide) (by decide)]
      exact supplyMorphoReadersFrame_params _ _ _ _ _ _
    have hbodyPrefix {result : ExecResult} (htail : ExecBlock config frame3 evm2 supplyMorphoSupply result) :
        ExecBlock config frame evm supplyMorphoIteration result := by
      apply hsource1.run
      apply ExecBlock.consNormal hskip
      apply hsource2
      exact execBlock_append harith htail
    rcases supplyMorphoAttemptSimulation (frame := frame3) v (marketParamsData params)
        (by simp only [List.append, List.length_cons]; omega) hl3 hp3
        (supplyMorphoArithmeticFrame_amount _ _ _ _ _ _) hs2 hfree2 hhi2 hsrc hspan (by omega)
        hloads (supplyMorphoAmount_le _ _ _ _ _) h4 with
      ⟨hbad, hrev⟩ | ⟨evm3, frame4, assets3, cursor, mem3, out3,
        hs3, hl4, hfree3, hhi3, hmono3, hprefix3, hattempt, scratch0, scratch1, aw5, k5, C5, h5⟩
    · exact .inl ⟨hbodyPrefix (ExecBlock.consRevert hbad), hrev⟩
    refine .inr ⟨evm3, frame4, assets3, cursor, mem3, out3, hs3, hl4, hfree3, hhi3,
      le_trans hmono2 hmono3, hprefix1.trans (hprefix2.trans (hprefix3.mono hmono2)), ?_⟩
    rcases supplyMorphoTailSimulation (frame := frame4) v (by omega) hl4.assets hl4.cursor hret h5 with
      ⟨_, hreturn, hdone⟩ | ⟨_, hnext, hdone⟩
    · exact .inl ⟨hbodyPrefix (ExecBlock.consNormal hattempt (ExecBlock.consReturn hreturn)), hdone⟩
    · exact .inr ⟨.inl (hbodyPrefix (ExecBlock.consNormal hattempt
        (ExecBlock.consNormal hnext ExecBlock.nil))), hdone⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
