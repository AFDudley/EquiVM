import Benchmarks.Morpho.MetaMorphoV1_1.DepositPublicSource
import Benchmarks.Morpho.MetaMorphoV1_1.DepositInternalSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.ConvertSharesRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.DepositEntry

/-! Public deposit after accrual, through share conversion and the internal deposit. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem depositPublicSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm0 evm : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {assets ptr ret : UInt256} {receiver : AccountAddress} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 30 ≤ 1024)
    (hs : SourceState s0 I σ evm) (hperm : I.perm = true)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hhi : ptr.toNat < 2 ^ 64)
    (hlo : 128 ≤ ptr.toNat) (hsize : 128 ≤ mem.size) (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨7392⟩
      ([UInt256.ofNat receiver.toNat, ret, assets] ++ R) mem aw rdata σ k C) :
    let shares := convertSharesWord v.DECIMALS_OFFSET assets
      (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
      (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨22⟩)
    (ExecBlock config (depositPublicAccruedFrame evm0 (immStore v) assets receiver ptr) evm
      depositPublicConversion .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (final : Frame) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      ExecBlock config (depositPublicAccruedFrame evm0 (immStore v) assets receiver ptr) evm
        depositPublicConversion (.returned final evm' (some [uint256Value shares])) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (shares :: R)
        mem' aw' out evm'.accountMap k' C' := by
  dsimp only
  let supply := Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩
  let total := Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨22⟩
  let shares := convertSharesWord v.DECIMALS_OFFSET assets supply total
  have hsup : codeOwnerStorageWord I σ ⟨2⟩ = supply := (hs.storageRead ⟨2⟩).symm
  have htot : codeOwnerStorageWord I σ ⟨22⟩ = total := (hs.storageRead ⟨22⟩).symm
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_7392_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  change RD (deployedRuntime v) I g s0 ⟨14489⟩
    ([assets, codeOwnerStorageWord I σ ⟨2⟩, codeOwnerStorageWord I σ ⟨22⟩,
      ⟨7408⟩, UInt256.ofNat receiver.toNat, ret, assets] ++ R) mem aw1 rdata σ k1 C1 at h1
  rw [hsup, htot] at h1
  by_cases hfit : convertSharesFits v.DECIMALS_OFFSET assets supply total
  · obtain ⟨aw2, k2, C2, h2⟩ := convertSharesReturn v
      (by simp only [List.append, List.length_cons]; omega) hfit
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
    obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_7408_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    rcases depositInternalSimulation v I.source receiver assets shares
        (by simp only [List.append, List.length_cons]; omega) hs hperm hcalldata
        hhi hlo hsize hfree hzero hret h3 with
      ⟨hbad, hrev⟩ | ⟨evm', final, cursor, mem', out, hs', hbody,
        _, _, _, _, aw4, k4, C4, h4⟩
    · rw [← hs.env] at hbad
      exact .inl ⟨depositPublicConversionContinue v hfit (depositPublicInternalReverts hbad), hrev⟩
    · rw [← hs.env] at hbody
      exact .inr ⟨evm', _, mem', out, hs',
        depositPublicConversionContinue v hfit (depositPublicInternalReturns hbody),
        aw4, k4, C4, h4⟩
  · exact .inl ⟨depositPublicConversionReverts v hfit,
      convertSharesRevert v (by simp only [List.append, List.length_cons]; omega) hfit h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
