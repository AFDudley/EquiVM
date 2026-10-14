import Benchmarks.Morpho.MetaMorphoV1_1.DelegateCallSource
import Benchmarks.Morpho.MetaMorphoV1_1.AddressVerifyRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.AddressVerifyBuffer
import Benchmarks.Morpho.MetaMorphoV1_1.CallReturnRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_022

/-! Couple multicall's return-buffer allocation and Address checks to its source helper. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem delegateCallPostSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm evm' : State}
    {mem data out : ByteArray} {aw : UInt256} {k C : Nat}
    {ptr ret : UInt256} {R : List UInt256} {ok : Bool}
    (v : MetaMorphoV1_1Immutables) (imms : Store)
    (hstack : R.length + 12 ≤ 1024) (hptr : ptr.toNat < 2 ^ 64)
    (hout : out.size < UInt256.size) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hcall : delegateCallViaEVM evm I.codeOwner data (ok, evm', out))
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨3961⟩
      ((if ok then ⟨1⟩ else ⟨0⟩) :: ret :: R) mem aw out evm'.accountMap k C) :
    (ExecFuncBody config (addressCallFrame imms I.codeOwner data ptr) evm
        allocatedDelegateCallFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
      (ok = true ∧ callReturnFits ptr out ∧
        ExecFuncBody config (addressCallFrame imms I.codeOwner data ptr) evm
          allocatedDelegateCallFunction.body
          (.returned (addressCallResultFrame imms I.codeOwner data ptr out) evm'
            (some [.bytes out, uint256Value (callReturnCursor ptr out)])) ∧
        ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
          (callReturnPointer ptr out :: R) (callReturnMemory mem ptr out)
          aw' out evm'.accountMap k' C') := by
  have r1 := metaMorphoV1_1_block_3961 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  rcases callReturnBuffer v (by
      simp only [List.length_cons]; omega) hptr hout hfree
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) r1 with
    ⟨hbad, hrev⟩ | ⟨hfit, aw2, k2, C2, r2⟩
  · exact .inl ⟨delegateCallBodyReverts imms I.codeOwner data ptr ok out hcall
      (.inl hbad), hrev⟩
  · have r3 := metaMorphoV1_1_block_3968 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
    cases ok with
    | false =>
        exact .inl ⟨delegateCallBodyReverts imms I.codeOwner data ptr false out hcall
          (.inr (.inl rfl)), addressVerifyRevertCall v
            (by omega) r3⟩
    | true =>
        by_cases hv : addressReturnValid evm' I.codeOwner out
        · exact .inr ⟨rfl, hfit,
            delegateCallBodyReturns imms I.codeOwner data ptr out hcall hfit hv,
            addressVerifyReturn v (by omega)
              ((addressReturnValid_memory hout hzero).mp hv) hret r3⟩
        · have hz : out.size = 0 := not_not.mp (fun hn ↦ hv (.inl hn))
          have hc : extCodeSizeWord evm'.accountMap (UInt256.ofNat I.codeOwner.toNat) = ⟨0⟩ :=
            not_not.mp (fun hn ↦ hv (.inr hn))
          exact .inl ⟨delegateCallBodyReverts imms I.codeOwner data ptr true out hcall
            (.inr (.inr hv)), addressVerifyRevertCode v
              (by omega)
              (by simpa only [hz] using callReturnMemory_length mem ptr out hzero) hc r3⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
