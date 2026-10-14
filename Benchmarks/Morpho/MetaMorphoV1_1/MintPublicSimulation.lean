import Benchmarks.Morpho.MetaMorphoV1_1.MintPublicSource
import Benchmarks.Morpho.MetaMorphoV1_1.DepositInternalSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.ConvertAssetsUpRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.MintEntry

/-! Public mint after accrual, through upward conversion and the shared deposit helper. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem mintPublicSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm0 evm : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {shares ptr ret : UInt256} {receiver : AccountAddress} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 30 ≤ 1024)
    (hs : SourceState s0 I σ evm) (hperm : I.perm = true)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hhi : ptr.toNat < 2 ^ 64)
    (hlo : 128 ≤ ptr.toNat) (hsize : 128 ≤ mem.size) (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨4831⟩
      ([shares, ret, UInt256.ofNat receiver.toNat] ++ R) mem aw rdata σ k C) :
    let assets := convertAssetsUpWord v.DECIMALS_OFFSET shares
      (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
      (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨22⟩)
    (ExecBlock config (mintPublicAccruedFrame evm0 (immStore v) shares receiver ptr) evm
      mintPublicConversion .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (final : Frame) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧
      ExecBlock config (mintPublicAccruedFrame evm0 (immStore v) shares receiver ptr) evm
        mintPublicConversion (.returned final evm' (some [uint256Value assets])) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (assets :: R)
        mem' aw' out evm'.accountMap k' C' := by
  dsimp only
  let supply := Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩
  let total := Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨22⟩
  let assets := convertAssetsUpWord v.DECIMALS_OFFSET shares supply total
  have hsup : codeOwnerStorageWord I σ ⟨2⟩ = supply := (hs.storageRead ⟨2⟩).symm
  have htot : codeOwnerStorageWord I σ ⟨22⟩ = total := (hs.storageRead ⟨22⟩).symm
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_4831_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  change RD (deployedRuntime v) I g s0 ⟨15275⟩
    ([shares, codeOwnerStorageWord I σ ⟨2⟩, codeOwnerStorageWord I σ ⟨22⟩,
      ⟨4847⟩, shares, ret, UInt256.ofNat receiver.toNat] ++ R) mem aw1 rdata σ k1 C1 at h1
  rw [hsup, htot] at h1
  by_cases hfit : convertAssetsUpFits v.DECIMALS_OFFSET shares supply total
  · obtain ⟨aw2, k2, C2, h2⟩ := convertAssetsUpReturn v
      (by simp only [List.append, List.length_cons]; omega) hfit
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
    obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_4847_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    rcases depositInternalSimulation v I.source receiver assets shares
        (by simp only [List.append, List.length_cons]; omega) hs hperm hcalldata
        hhi hlo hsize hfree hzero hret h3 with
      ⟨hbad, hrev⟩ | ⟨evm', final, cursor, mem', out, hs', hbody,
        _, _, _, _, aw4, k4, C4, h4⟩
    · rw [← hs.env] at hbad
      exact .inl ⟨(mintPublicConversionPrefix v hfit).run (mintPublicInternalReverts hbad), hrev⟩
    · rw [← hs.env] at hbody
      exact .inr ⟨evm', _, mem', out, hs',
        (mintPublicConversionPrefix v hfit).run (mintPublicInternalReturns hbody),
        aw4, k4, C4, h4⟩
  · exact .inl ⟨mintPublicConversionReverts v hfit,
      convertAssetsUpRevert v (by simp only [List.append, List.length_cons]; omega) hfit h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
