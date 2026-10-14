import Benchmarks.Morpho.MetaMorphoV1_1.DepositInternalSource
import Benchmarks.Morpho.MetaMorphoV1_1.DepositFinishSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.ERC4626DepositSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoSimulation

/-! Complete internal deposit simulation, including token movement and market supply. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem depositInternalSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (caller receiver : AccountAddress) (assets shares : UInt256)
    (hstack : R.length + 29 ≤ 1024) (hs : SourceState s0 I σ evm) (hperm : I.perm = true)
    (hcalldata : I.calldata.size < UInt256.size)
    (hptr : ptr.toNat < 2 ^ 64) (hlo : 128 ≤ ptr.toNat) (hsize : 128 ≤ mem.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨14558⟩
      ([UInt256.ofNat caller.toNat, UInt256.ofNat receiver.toNat, assets, shares, ret] ++ R)
      mem aw rdata σ k C) :
    (ExecFuncBody config (erc4626DepositFrame (immStore v) caller receiver assets shares ptr)
        evm allocatedDepositFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (cursor : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      ExecFuncBody config (erc4626DepositFrame (immStore v) caller receiver assets shares ptr)
        evm allocatedDepositFunction.body (.returned frame' evm' (some [uint256Value cursor])) ∧
      cursor.toNat < 2 ^ 64 ∧ ptr.toNat ≤ cursor.toNat ∧ MemoryPrefix mem mem' ptr.toNat ∧
      memLoad ⟨64⟩ mem' = cursor ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret R mem' aw' out evm'.accountMap k' C' := by
  rcases erc4626DepositSimulation v caller receiver assets shares
      (by simp only [List.append, List.length_cons]; omega) hs hperm hptr hlo hsize hfree hzero rd with
    ⟨hbad, hrev⟩ | ⟨evm1, cursor1, mem1, out1, aw1, k1, C1, hs1, hsource1,
      hhi1, hmono1, hprefix1, hfree1, h1⟩
  · exact .inl ⟨depositERC4626Reverts hbad, hrev⟩
  have hcall1 := depositERC4626Call hsource1
  rcases supplyMorphoSimulation v
      (by simp only [List.append, List.length_cons]; omega) hcalldata hfree1 (by omega) hhi1
      (by have hm := hprefix1.size; omega) hs1
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1 with
    ⟨hbad, hrev⟩ | ⟨evm2, final2, cursor2, mem2, out2,
      hs2, hsource2, hfree2, hhi2, hmono2, hprefix2, aw2, k2, C2, h2⟩
  · refine .inl ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    rw [allocatedDepositFunction_body]
    exact ExecBlock.consNormal hcall1 (depositSupplyReverts hbad)
  let frame2 := depositSuppliedFrame (immStore v) caller receiver assets shares ptr cursor1 cursor2
  have hcall2 := depositSupplyCall (caller := caller) (receiver := receiver)
    (shares := shares) (ptr := ptr) hsource2
  rcases depositFinishSimulation (frame := frame2) v (by omega) rfl
      (depositSuppliedFrame_lastAssets _ _ _ _ _ _ _ _)
      (depositSuppliedFrame_assets _ _ _ _ _ _ _ _) (cursorResultFrame_cursor _ _ _ _)
      hfree2 (by omega) (by have hm1 := hprefix1.size; have hm2 := hprefix2.size; omega)
      hs2 hperm hret h2 with
    ⟨hbad, hrev⟩ | ⟨evm3, mem3, hs3, hsource3, hfree3, hprefix3, hdone⟩
  · refine .inl ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    rw [allocatedDepositFunction_body]
    exact ExecBlock.consNormal hcall1 (cursorCallPrefix (by decide) hcall2 hbad)
  · refine .inr ⟨evm3, depositUpdatedFrame frame2, cursor2, mem3, out2, hs3,
      ExecFuncBody.execBlockRet ?_, hhi2, le_trans hmono1 hmono2,
      hprefix1.trans ((hprefix2.trans (hprefix3.mono hmono2)).mono hmono1), hfree3, hdone⟩
    rw [allocatedDepositFunction_body]
    exact ExecBlock.consNormal hcall1 (cursorCallPrefix (by decide) hcall2 hsource3)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
