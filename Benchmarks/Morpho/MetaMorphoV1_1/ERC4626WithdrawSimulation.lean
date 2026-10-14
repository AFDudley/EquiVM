import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawAllowanceSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawBurnRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.SafeTransferRoutines

/-! Full ERC4626 withdrawal: optional allowance, burn, token transfer, and event. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem erc4626WithdrawSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (caller receiver owner : AccountAddress) (assets shares : UInt256)
    (hstack : R.length + 22 ≤ 1024) (hs : SourceState s0 I σ evm) (hperm : I.perm = true)
    (hptr : ptr.toNat < 2 ^ 64) (hlo : 128 ≤ ptr.toNat) (hsize : 128 ≤ mem.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨15554⟩
      ([shares, UInt256.ofNat receiver.toNat, UInt256.ofNat caller.toNat, assets,
        UInt256.ofNat owner.toNat, ret] ++ R) mem aw rdata σ k C) :
    (ExecFuncBody config (erc4626WithdrawFrame (immStore v) caller receiver owner assets shares ptr)
        evm allocatedERC4626WithdrawFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (cursor : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      ExecFuncBody config (erc4626WithdrawFrame (immStore v) caller receiver owner assets shares ptr)
        evm allocatedERC4626WithdrawFunction.body (.returned frame' evm' [uint256Value cursor]) ∧
      cursor.toNat < 2 ^ 64 ∧ ptr.toNat ≤ cursor.toNat ∧ MemoryPrefix mem mem' ptr.toNat ∧
      memLoad ⟨64⟩ mem' = cursor ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R mem' aw' out evm'.accountMap k' C' := by
  rcases withdrawAllowanceSimulation v (by omega)
      (erc4626WithdrawInitialLocals v caller receiver owner assets shares ptr)
      hs hperm hfree (by omega) rd with
    ⟨hbad, hrev⟩ | ⟨evm1, frame1, mem1, hs1, hl1, hallowance, hfree1, hprefix1,
      scratch0, scratch1, scratch2, aw1, k1, C1, h1⟩
  · refine .inl ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    rw [allocatedERC4626WithdrawFunction_body]
    exact ExecBlock.consRevert hbad
  rcases frame1 with ⟨c, locals, imms⟩
  have hc := hl1.contract
  have hi := hl1.imms
  dsimp only at hc hi
  subst c
  subst imms
  let frame1 : Frame := ⟨contract, locals, immStore v⟩
  have hargs1 := withdrawVaultBurnArgs (evm := evm1) hl1
  rw [← hs1.env] at h1
  rcases withdrawBurnSimulation v (by omega) (by rw [hs1.env]; exact hperm)
      hfree1 (by have hm := hprefix1.size; omega) (by omega) h1 with
    ⟨hbad, hrev⟩ | ⟨hgood, mem2, aw2, k2, C2, hfree2, hprefix2, h2⟩
  · refine .inl ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    rw [allocatedERC4626WithdrawFunction_body]
    exact ExecBlock.consNormal hallowance (ExecBlock.consRevert (burnCallReverts hargs1 hbad))
  let evm2 := burnBalanceState evm1 owner shares
  let frame2 := { frame1 with locals := frame1.locals.insert "__c1" .unit }
  have hs2 := burnBalanceSourceState hs1 owner shares
  have hl2 : WithdrawVaultLocals v frame2 caller receiver owner assets shares ptr :=
    hl1.insert "__c1" .unit (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hburn := burnCall (ret := "__c1") hargs1 hgood
  rw [hs1.env] at h2
  have hprefix12 := hprefix1.trans hprefix2
  have hmem2 : 128 ≤ mem2.size := le_trans hsize hprefix12.size
  have hzero2 : memLoad ⟨96⟩ mem2 = ⟨0⟩ :=
    (hprefix12.load_preserved (off := 96) (by decide) hlo hsize (by decide)).trans hzero
  rcases safeTransferHeapSimulation v (immStore v) v._asset receiver assets
      (by simp only [List.append, List.length_cons]; omega) hs2 hptr hlo hmem2 hfree2 hzero2
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2 with
    ⟨hbad, hrev⟩ | ⟨evm3, cursor, mem3, out3, aw3, k3, C3,
      hs3, hsource3, hhi3, hmono3, hprefix3, hfree3, h3⟩
  · refine .inl ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    rw [allocatedERC4626WithdrawFunction_body]
    apply ExecBlock.consNormal hallowance
    apply ExecBlock.consNormal hburn
    exact ExecBlock.consRevert (internalCallFunctionRevert (callee := allocatedSafeTransferFunction)
      (withdrawVaultTransferArgs (evm := evm2) hl2) rfl rfl hbad)
  have htransfer := internalCallFunctionReturn (retVar := cursorName)
    (name := allocatedSafeTransferFunction.name) (callee := allocatedSafeTransferFunction)
    (withdrawVaultTransferArgs (evm := evm2) hl2) rfl rfl hsource3
  let frame3 := { frame2 with locals := frame2.locals.insert cursorName (uint256Value cursor) }
  have hl3 : WithdrawVaultLocals v frame3 caller receiver owner assets shares cursor := hl2.withCursor cursor
  obtain ⟨aw4, k4, C4, h4⟩ := metaMorphoV1_1_block_15753_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
    hperm hret h3
  have hmem3 : 128 ≤ mem3.size := le_trans hmem2 hprefix3.size
  have hfree4 := accrueInterestFinishMemory_free assets shares hfree3 (by omega) (by omega) hhi3
  have hprefix4 := accrueInterestFinishMemory_prefix assets shares hfree3 hhi3
  refine .inr ⟨evm3, frame3, cursor, accrueInterestFinishMemory mem3 assets shares, out3, hs3,
    ExecFuncBody.execBlockRet ?_, hhi3, hmono3,
    hprefix12.trans (hprefix3.trans (hprefix4.mono hmono3)), hfree4, aw4, k4, C4, h4⟩
  rw [allocatedERC4626WithdrawFunction_body]
  exact ExecBlock.consNormal hallowance (ExecBlock.consNormal hburn
    (ExecBlock.consNormal htransfer (withdrawVaultFinishSource hl3)))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
