import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawInternalSource
import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawMorphoSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.ERC4626WithdrawSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.UpdateLastAssetsRoutines

/-! Complete internal withdrawal, from accounting through market withdrawal and payment. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem withdrawInternalSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (caller receiver owner : AccountAddress) (assets shares : UInt256)
    (hstack : R.length + 34 ≤ 1024) (hs : SourceState s0 I σ evm) (hperm : I.perm = true)
    (hcalldata : I.calldata.size < UInt256.size)
    (hptr : ptr.toNat < 2 ^ 64) (hlo : 128 ≤ ptr.toNat) (hsize : 128 ≤ mem.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨15525⟩
      ([UInt256.ofNat caller.toNat, UInt256.ofNat receiver.toNat, UInt256.ofNat owner.toNat,
        assets, shares, ret] ++ R) mem aw rdata σ k C) :
    (ExecFuncBody config (erc4626WithdrawFrame (immStore v) caller receiver owner assets shares ptr)
        evm allocatedWithdrawFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (cursor : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      ExecFuncBody config (erc4626WithdrawFrame (immStore v) caller receiver owner assets shares ptr)
        evm allocatedWithdrawFunction.body (.returned frame' evm' [uint256Value cursor]) ∧
      cursor.toNat < 2 ^ 64 ∧ ptr.toNat ≤ cursor.toNat ∧ MemoryPrefix mem mem' ptr.toNat ∧
      memLoad ⟨64⟩ mem' = cursor ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R mem' aw' out evm'.accountMap k' C' := by
  let remaining := withdrawRemainingAssets evm assets
  let frame0 := erc4626WithdrawFrame (immStore v) caller receiver owner assets shares ptr
  let frame1 := withdrawAccountingFrame frame0 remaining
  let evm1 := updateLastAssetsState evm remaining
  let mem1 := writeWord mem ptr.toNat remaining
  have hl0 := erc4626WithdrawInitialLocals v caller receiver owner assets shares ptr
  have hl1 : WithdrawVaultLocals v frame1 caller receiver owner assets shares ptr := hl0.accounting remaining
  have hacct := withdrawAccountingSource (frame := frame0) (evm := evm) rfl
    (by simp [frame0, erc4626WithdrawFrame, cursorName, Std.HashMap.getElem_insert]) hl0.assets
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_15525_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [metaMorphoV1_1_block_15525_stack, wordZeroFloorSub] at h1
  have hpast := hs.storageRead ⟨22⟩
  change Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨22⟩ = codeOwnerStorageWord I σ ⟨22⟩ at hpast
  change RD (deployedRuntime v) I g s0 ⟨16830⟩
    ([UInt256.ofNat ((codeOwnerStorageWord I σ ⟨22⟩).toNat - assets.toNat), ⟨15545⟩,
      shares, UInt256.ofNat receiver.toNat, UInt256.ofNat caller.toNat, assets,
      UInt256.ofNat owner.toNat, ret] ++ R) mem aw1 rdata σ k1 C1 at h1
  rw [← hpast] at h1
  change RD (deployedRuntime v) I g s0 ⟨16830⟩
    ([remaining, ⟨15545⟩, shares, UInt256.ofNat receiver.toNat, UInt256.ofNat caller.toNat,
      assets, UInt256.ofNat owner.toNat, ret] ++ R) mem aw1 rdata σ k1 C1 at h1
  rw [hs.accounts, ← hs.env] at h1
  obtain ⟨aw2, k2, C2, h2⟩ := updateLastAssetsReturn v
    (by simp only [List.append, List.length_cons]; omega) (by rw [hs.env]; exact hperm)
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  rw [hs.env, hfree] at h2
  have hs1 : SourceState s0 I evm1.accountMap evm1 := sourceStateStoreSelf hs ⟨22⟩ remaining
  have hf1 : memLoad ⟨64⟩ mem1 = ptr := writeFreeWord_free _ hfree (by omega) (by omega)
  have hpre1 : MemoryPrefix mem mem1 ptr.toNat :=
    memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _))
  obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_15545_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
  rcases withdrawMorphoSimulation v (by simp only [List.append, List.length_cons]; omega)
      hcalldata hf1 (by omega) hptr (by have hm := hpre1.size; omega) hs1
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h3 with
    ⟨hbad, hrev⟩ | ⟨evm2, final2, cursor2, mem2, out2, hs2, hsource2,
      hfree2, hhi2, hmono2, hpre2, aw4, k4, C4, h4⟩
  · refine .inl ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    rw [allocatedWithdrawFunction_body]
    apply execBlock_append_ok hacct
    exact ExecBlock.consRevert (internalCallFunctionRevert (callee := allocatedWithdrawMorphoFunction)
      (withdrawMarketArgs (evm := evm1) hl1) allocatedWithdrawMorphoFunction_lookup rfl hbad)
  have hcall2 := internalCallFunctionReturn (retVar := slotsAndCursorName)
    (name := allocatedWithdrawMorphoFunction.name) (callee := allocatedWithdrawMorphoFunction)
    (withdrawMarketArgs (evm := evm1) hl1) allocatedWithdrawMorphoFunction_lookup rfl hsource2
  let frame2 := cursorResultFrame frame1 "__c2" (.tuple []) cursor2
  have hl2 : WithdrawVaultLocals v frame2 caller receiver owner assets shares cursor2 := hl1.market cursor2
  have hpre12 := hpre1.trans hpre2
  have hzero2 : memLoad ⟨96⟩ mem2 = ⟨0⟩ :=
    (hpre12.load_preserved (off := 96) (by decide) hlo hsize (by decide)).trans hzero
  rcases erc4626WithdrawSimulation v caller receiver owner assets shares (by omega) hs2 hperm
      hhi2 (by omega) (le_trans hsize hpre12.size) hfree2 hzero2 hret h4 with
    ⟨hbad, hrev⟩ | ⟨evm3, final3, cursor3, mem3, out3, hs3, hsource3,
      hhi3, hmono3, hpre3, hfree3, hdone⟩
  · refine .inl ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    rw [allocatedWithdrawFunction_body]
    apply execBlock_append_ok hacct
    apply cursorCallPrefix (by decide) hcall2
    exact ExecBlock.consRevert (internalCallFunctionRevert (callee := allocatedERC4626WithdrawFunction)
      (withdrawVaultArgs (evm := evm2) hl2) rfl rfl hbad)
  have hcall3 := internalCallFunctionReturn (retVar := cursorName)
    (name := allocatedERC4626WithdrawFunction.name) (callee := allocatedERC4626WithdrawFunction)
    (withdrawVaultArgs (evm := evm2) hl2) rfl rfl hsource3
  refine .inr ⟨evm3, resumeAfterInternalCall frame2 cursorName (some [uint256Value cursor3]),
    cursor3, mem3, out3, hs3, ExecFuncBody.execBlockRet ?_, hhi3,
    le_trans hmono2 hmono3, hpre1.trans (hpre2.trans (hpre3.mono hmono2)), hfree3, hdone⟩
  rw [allocatedWithdrawFunction_body]
  apply execBlock_append_ok hacct
  apply cursorCallPrefix (by decide) hcall2
  apply ExecBlock.consNormal hcall3
  exact ExecBlock.consReturn (ExecStmt.return (by
    simp only [evalExprs?, evalExpr?, resumeAfterInternalCall, collapseReturns,
      store_get_self, EvalResult.ofOption, bind, EvalResult.bind, pure]))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
