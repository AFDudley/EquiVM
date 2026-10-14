import Benchmarks.Morpho.MetaMorphoV1_1.ERC4626DepositSource
import Benchmarks.Morpho.MetaMorphoV1_1.DepositTokenTransfer
import Benchmarks.Morpho.MetaMorphoV1_1.AccrueInterestSimulation

/-! The complete ERC4626 deposit prefix, ending at the market-supply routine. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

def depositBeforeSupplyStack (assets : UInt256) (R : List UInt256) : List UInt256 :=
  [assets, ⟨14745⟩, assets, ⟨13745⟩, ⟨14753⟩] ++ R

theorem erc4626DepositSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (caller receiver : AccountAddress) (assets shares : UInt256)
    (hstack : R.length + 21 ≤ 1024) (hs : SourceState s0 I σ evm) (hperm : I.perm = true)
    (hptr : ptr.toNat < 2 ^ 64) (hlo : 128 ≤ ptr.toNat) (hsize : 128 ≤ mem.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨14558⟩
      ([UInt256.ofNat caller.toNat, UInt256.ofNat receiver.toNat, assets, shares] ++ R)
      mem aw rdata σ k C) :
    (ExecFuncBody config (erc4626DepositFrame (immStore v) caller receiver assets shares ptr)
        evm allocatedERC4626DepositFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
      ∃ (evm' : State) (cursor : UInt256) (mem' out : ByteArray) (aw' : UInt256) (k' C' : Nat),
        SourceState s0 I evm'.accountMap evm' ∧
        ExecFuncBody config (erc4626DepositFrame (immStore v) caller receiver assets shares ptr)
          evm allocatedERC4626DepositFunction.body
          (.returned (erc4626DepositResultFrame (immStore v) caller receiver assets shares ptr cursor)
            evm' [uint256Value cursor]) ∧
        cursor.toNat < 2 ^ 64 ∧ ptr.toNat ≤ cursor.toNat ∧ MemoryPrefix mem mem' ptr.toNat ∧
        memLoad ⟨64⟩ mem' = cursor ∧
        RD (deployedRuntime v) I g s0 ⟨17891⟩ (depositBeforeSupplyStack assets R)
          mem' aw' out evm'.accountMap k' C' := by
  rcases depositTokenTransferSimulation v caller receiver assets shares hstack hs hptr hlo hsize
      hfree hzero rd with
    ⟨hsource, hrev⟩ | ⟨evm1, cursor, mem1, out, aw1, k1, C1, hs1, hsource,
      hhi1, hmono1, hpre1, hfree1, h1⟩
  · rw [← hs.env] at hsource
    exact .inl ⟨erc4626DepositTransferReverts v caller receiver assets shares ptr hsource, hrev⟩
  rw [← hs.env] at hsource
  simp only [depositAfterTransferStack, List.cons_append, List.nil_append] at h1
  have h2 := metaMorphoV1_1_block_14702 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  simp only [metaMorphoV1_1_block_14702_stack] at h2
  rw [← hs1.env] at h2
  by_cases hgood : mintAllowed evm1 receiver shares
  · have hp1 : evm1.executionEnv.perm = true := by rw [hs1.env]; exact hperm
    obtain ⟨aw3, k3, C3, h3⟩ := mintReturn v (by simp only [List.length_cons]; omega)
      hgood hp1 (by rw [metaMorphoV1_1PatchedValidJumps]; jump_dest) h2
    rw [hs1.env] at h3
    obtain ⟨aw4, k4, C4, h4⟩ := metaMorphoV1_1_block_14712_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hperm
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
    have hm1 : 128 ≤ mem1.size := le_trans hsize hpre1.size
    have hf3 := mintReturnMemory_free receiver shares hfree1 (by omega) (by omega)
    have hp3 := mintReturnMemory_prefix receiver shares hfree1 (by omega)
    have hm3 := le_trans hm1 hp3.size
    have hf4 := accrueInterestFinishMemory_free assets shares hf3 (by omega) (by omega) hhi1
    have hp4 := accrueInterestFinishMemory_prefix assets shares hf3 hhi1
    exact .inr ⟨_, cursor, _, out, aw4, k4, C4, mintBalanceSourceState hs1 receiver shares,
      ExecFuncBody.execBlockRet (erc4626DepositTransferPrefix v caller receiver assets shares
        ptr cursor hsource (erc4626DepositMintReturns evm1 (immStore v) caller receiver
          assets shares ptr cursor hgood)), hhi1, hmono1,
      hpre1.trans ((hp3.trans hp4).mono hmono1), hf4, h4⟩
  · exact .inl ⟨ExecFuncBody.execBlockRevert
      (erc4626DepositTransferPrefix v caller receiver assets shares ptr cursor hsource
        (erc4626DepositMintReverts evm1 (immStore v) caller receiver assets shares ptr cursor hgood)),
      mintRevert v (by simp only [List.length_cons]; omega) hgood h2⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
