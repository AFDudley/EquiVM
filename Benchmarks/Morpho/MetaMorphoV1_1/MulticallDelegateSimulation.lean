import Benchmarks.Morpho.MetaMorphoV1_1.DelegateCallRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.StringBuffer

/-! The complete allocated self-DELEGATECALL used by each multicall iteration. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem multicallDelegateSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata data : ByteArray} {aw : UInt256} {k C : Nat}
    {input ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (imms : Store)
    (hstack : R.length + 12 ≤ 1024) (hptr : ptr.toNat < 2 ^ 64)
    (hinput : input.toNat + 32 < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hdata : StringBuffer mem input.toNat data) (hsize : data.size < UInt256.size)
    (hs : SourceState s0 I evm.accountMap evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨3951⟩
      (input :: ⟨0⟩ :: ⟨0⟩ :: ret :: R) mem aw rdata evm.accountMap k C) :
    (ExecFuncBody config (addressCallFrame imms I.codeOwner data ptr) evm
        allocatedDelegateCallFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
      ∃ (evm' : State) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
        SourceState s0 I evm'.accountMap evm' ∧ callReturnFits ptr out ∧
        ExecFuncBody config (addressCallFrame imms I.codeOwner data ptr) evm
          allocatedDelegateCallFunction.body
          (.returned (addressCallResultFrame imms I.codeOwner data ptr out) evm'
            (some [.bytes out, uint256Value (callReturnCursor ptr out)])) ∧
        RD (deployedRuntime v) I g s0 ret (callReturnPointer ptr out :: R)
          (callReturnMemory mem ptr out) aw' out evm'.accountMap k' C' := by
  have r1 := metaMorphoV1_1_block_3951 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) rd
  have hd : memLoad input mem = UInt256.ofNat data.size := by
    simpa only [u256_ofNat_toNat] using hdata.length
  have hr : mem.readWithPadding (input + ⟨32⟩).toNat (memLoad input mem).toNat = data := by
    have hp : (input + (⟨32⟩ : UInt256)).toNat = input.toNat + 32 :=
      uadd_word_ofNat_toNat input 32 hinput
    rw [hd, UInt256.toNat_ofNat_of_lt hsize, hp]
    exact hdata.data
  obtain ⟨evm', ok, out, aw2, k2, C2, hcall, hs', hout, r2⟩ := delegateCallSimulation
    (by simp only [List.length_cons]; omega)
    (by immutable_decode(Benchmarks.Morpho.MetaMorphoV1_1.immutableLayout,
      Benchmarks.Morpho.MetaMorphoV1_1.metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨3960⟩ : UInt256), UInt8.ofNat 244, .DELEGATECALL, none,
      immutableLayout_inBounds, immutableTemplate_size64))
    hs (by exact (accountAddress_roundtrip I.codeOwner).symm) hr r1
  rw [callOutputMem_zero] at r2
  rcases delegateCallPostSimulation v imms hstack hptr hout hfree hzero hcall hret r2 with
    ⟨hbody, hrev⟩ | ⟨_, hfit, hbody, aw3, k3, C3, r3⟩
  · exact .inl ⟨hbody, hrev⟩
  · exact .inr ⟨evm', out, aw3, k3, C3, hs', hfit, hbody, r3⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
