import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawMorphoQueue
import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawMorphoReadersSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawMorphoMinimum
import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawMorphoAttempt
import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawMorphoTail

/-! One complete mutating withdrawal iteration and its early return. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem withdrawMorphoIterationSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr assets ret i : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 28 ≤ 1024)
    (hl : WithdrawMorphoLocals v frame i assets ptr)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hmem : 96 ≤ mem.size) (hs : SourceState s0 I σ evm)
    (hbound : i.toNat < (codeOwnerStorageWord I σ ⟨21⟩).toNat)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨18674⟩
      ([i, assets, ret] ++ R) mem aw rdata σ k C) :
    (ExecBlock config frame evm withdrawMorphoIteration .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (assets' cursor : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧ WithdrawMorphoLocals v frame' i assets' cursor ∧
      memLoad ⟨64⟩ mem' = cursor ∧ cursor.toNat < 2 ^ 64 ∧ ptr.toNat ≤ cursor.toNat ∧
      MemoryPrefix mem mem' ptr.toNat ∧
      ((ExecBlock config frame evm withdrawMorphoIteration
          (.returned frame' evm' (some [.tuple [], uint256Value cursor])) ∧
        ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R mem' aw' out evm'.accountMap k' C') ∨
       (ExecBlock config frame evm withdrawMorphoIteration (.ok frame' evm') ∧
        ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨18765⟩
          ([i, assets', ret] ++ R) mem' aw' out evm'.accountMap k' C')) := by
  have hread := accruedAssetsQueueRead hl.contract hl.queue hl.index
    (by rw [hs.storageRead]; exact hbound)
  rw [hs.storageRead] at hread
  let id := accruedAssetsIdWord I σ i
  let frame1 := { frame with locals := frame.locals.insert "id" (wordBytes32Value id) }
  let mem1 := wordAt0Mem ⟨21⟩ mem
  have hl1 : WithdrawMorphoLocals v frame1 i assets ptr := hl.insert "id" _
    (by decide) (by decide) (by decide) (by decide) (by decide)
  have hprefix1 : MemoryPrefix mem mem1 ptr.toNat :=
    memoryPrefix_sparse_writeWord _ _ _ _ (.inr (by decide))
  obtain ⟨aw1, k1, C1, h1⟩ := withdrawMorphoQueueRoutine v
    (by simp only [List.append, List.length_cons]; omega) hbound rd
  rcases withdrawMorphoReadersSimulation (frame := frame1) v
      (by simp only [List.append, List.length_cons]; omega) hl1 (store_get_self _ _ _) hcalldata
      ((accruedAssetsQueueMemory_free hmem).trans hfree) hlo hs h1 with
    ⟨hbad, hrev⟩ | ⟨evm2, frame2, p, mem2, out2, src, ptr2, liquidity,
      hs2, hl2, hp2, ht2, hsource2, hfree2, hlo2, hhi2, hmem2, hmono2,
      hprefix2, hsrc, hspan, hloads, aw2, k2, C2, h2⟩
  · exact .inl ⟨ExecBlock.consNormal (ExecStmt.letDecl hread) (hbad _), hrev⟩
  let amount := minimumWord liquidity assets
  let frame3 := withdrawMorphoMinimumFrame frame2 liquidity assets
  have hl3 : WithdrawMorphoLocals v frame3 i assets ptr2 :=
    hl2.insert "toWithdraw" _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have hp3 : frame3.locals.get? "marketParams" = some p.value := by
    rw [show frame3 = withdrawMorphoMinimumFrame frame2 liquidity assets from rfl,
      withdrawMorphoMinimumFrame, store_get_ne _ _ (by decide)]
    exact hp2
  have hmin := withdrawMorphoMinimumSource (evm := evm2) hl2.contract ht2 hl2.assets
  obtain ⟨aw3, k3, C3, h3⟩ := withdrawMorphoMinimumReach v
    (by simp only [List.append, List.length_cons]; omega) h2
  have hbodyPrefix {result : ExecResult}
      (htail : ExecBlock config frame3 evm2 withdrawMorphoAttempt result) :
      ExecBlock config frame evm withdrawMorphoIteration result := by
    apply ExecBlock.consNormal (ExecStmt.letDecl hread)
    apply hsource2
    exact ExecBlock.consNormal hmin htail
  have hsub : amount.toNat ≤ assets.toNat := by
    rw [minimumWord_toNat]
    exact Nat.min_le_right _ _
  rcases withdrawMorphoAttemptSimulation (frame := frame3) v p
      (by simp only [List.append, List.length_cons]; omega) hl3 hp3 (store_get_self _ _ _) hs2 hfree2 hhi2
      hsrc hspan (by omega) hloads hsub h3 with
    ⟨hbad, hrev⟩ | ⟨evm3, frame4, assets3, cursor, mem3, out3,
      hs3, hl4, hfree3, hhi3, hmono3, hprefix3, hattempt, scratch0, scratch1, aw4, k4, C4, h4⟩
  · exact .inl ⟨hbodyPrefix (ExecBlock.consRevert hbad), hrev⟩
  refine .inr ⟨evm3, frame4, assets3, cursor, mem3, out3, hs3, hl4, hfree3, hhi3,
    le_trans hmono2 hmono3, hprefix1.trans (hprefix2.trans (hprefix3.mono hmono2)), ?_⟩
  rcases withdrawMorphoTailSimulation (frame := frame4) v (by omega) hl4.assets hl4.cursor hret h4 with
    ⟨_, hreturn, hdone⟩ | ⟨_, hnext, hdone⟩
  · exact .inl ⟨hbodyPrefix (ExecBlock.consNormal hattempt (ExecBlock.consReturn hreturn)), hdone⟩
  · exact .inr ⟨hbodyPrefix (ExecBlock.consNormal hattempt
      (ExecBlock.consNormal hnext ExecBlock.nil)), hdone⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
