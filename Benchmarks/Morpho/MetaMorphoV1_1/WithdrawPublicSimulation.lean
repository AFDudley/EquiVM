import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawPublicSource
import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawInternalSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.ConvertSharesUpRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_020

/-! Public withdrawal after accrual, through upward conversion and internal withdrawal. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem withdrawPublicSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm0 evm : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {assets ptr ret : UInt256} {receiver owner : AccountAddress} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 35 ≤ 1024)
    (hs : SourceState s0 I σ evm) (hperm : I.perm = true)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hhi : ptr.toNat < 2 ^ 64)
    (hlo : 128 ≤ ptr.toNat) (hsize : 128 ≤ mem.size) (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨3475⟩
      ([assets, UInt256.ofNat receiver.toNat, ret, UInt256.ofNat owner.toNat] ++ R) mem aw rdata σ k C) :
    let shares := convertSharesUpWord v.DECIMALS_OFFSET assets
      (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
      (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨22⟩)
    (ExecBlock config (withdrawPublicAccruedFrame evm0 (immStore v) assets receiver owner ptr) evm
      withdrawPublicConversion .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (final : Frame) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      ExecBlock config (withdrawPublicAccruedFrame evm0 (immStore v) assets receiver owner ptr) evm
        withdrawPublicConversion (.returned final evm' (some [uint256Value shares])) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (shares :: R)
        mem' aw' out evm'.accountMap k' C' := by
  dsimp only
  let supply := Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩
  let total := Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨22⟩
  let shares := convertSharesUpWord v.DECIMALS_OFFSET assets supply total
  have hsup : codeOwnerStorageWord I σ ⟨2⟩ = supply := (hs.storageRead ⟨2⟩).symm
  have htot : codeOwnerStorageWord I σ ⟨22⟩ = total := (hs.storageRead ⟨22⟩).symm
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_3475_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  change RD (deployedRuntime v) I g s0 ⟨14419⟩
    ([assets, codeOwnerStorageWord I σ ⟨2⟩, codeOwnerStorageWord I σ ⟨22⟩,
      ⟨3491⟩, assets, UInt256.ofNat receiver.toNat, ret, UInt256.ofNat owner.toNat] ++ R) mem aw1 rdata σ k1 C1 at h1
  rw [hsup, htot] at h1
  by_cases hfit : convertSharesUpFits v.DECIMALS_OFFSET assets supply total
  · obtain ⟨aw2, k2, C2, h2⟩ := convertSharesUpReturn v
      (by simp only [List.append, List.length_cons]; omega) hfit
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
    obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_3491_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    rcases withdrawInternalSimulation v I.source receiver owner assets shares
        (by simp only [List.append, List.length_cons]; omega) hs hperm hcalldata
        hhi hlo hsize hfree hzero hret h3 with
      ⟨hbad, hrev⟩ | ⟨evm', final, cursor, mem', out, hs', hbody,
        _, _, _, _, aw4, k4, C4, h4⟩
    · rw [← hs.env] at hbad
      exact .inl ⟨(withdrawPublicConversionPrefix v hfit).run (withdrawPublicInternalReverts hbad), hrev⟩
    · rw [← hs.env] at hbody
      exact .inr ⟨evm', _, mem', out, hs',
        (withdrawPublicConversionPrefix v hfit).run (withdrawPublicInternalReturns hbody),
        aw4, k4, C4, h4⟩
  · exact .inl ⟨withdrawPublicConversionReverts v hfit,
      convertSharesUpRevert v (by simp only [List.append, List.length_cons]; omega) hfit h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
