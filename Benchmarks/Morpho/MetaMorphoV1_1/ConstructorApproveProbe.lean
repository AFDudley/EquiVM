import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorApproveCall
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorOptionalBoolRead
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorCallReturn
import Benchmarks.Morpho.MetaMorphoV1_1.OptionalBoolCallSource

/-! First approval: shared CALL, raw-return allocation, strict decoding, and fallback decision. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

theorem constructorApproveProbe {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem rdata : ByteArray} {aw request ptr gasArg : UInt256}
    {σ : AccountMap} {k C : Nat} (imms : Store) (asset spender : AccountAddress)
    (hr : request.toNat < 2 ^ 64) (hp : ptr.toNat < 2 ^ 64)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hbuffer : BytesBuffer mem request (constructorApproveCalldata spender constructorApprovalValue))
    (hs : SourceState s0 I σ evm)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1126⟩
      [gasArg, UInt256.ofNat asset.val, ⟨0⟩, request + ⟨32⟩, ⟨68⟩, ⟨0⟩, ⟨0⟩,
        UInt256.ofNat spender.val, UInt256.ofNat asset.val, request, ⟨32⟩, ⟨64⟩]
      mem aw rdata σ k C) :
    (ExecFuncBody config
        (optionalCallFrame imms asset (constructorApproveCalldata spender constructorApprovalValue) ptr)
        evm allocatedOptionalReturnBoolFunction.body .reverted ∧
      RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    (∃ (evm' : State) (ok : Bool) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      SourceState s0 I evm'.accountMap evm' ∧ callReturnFits ptr out ∧
      ExecFuncBody config
        (optionalCallFrame imms asset (constructorApproveCalldata spender constructorApprovalValue) ptr)
        evm allocatedOptionalReturnBoolFunction.body
        (.returned (optionalBoolResultFrame imms asset
          (constructorApproveCalldata spender constructorApprovalValue) ptr ok out) evm'
          (some [.bool (optionalBoolValue evm'.accountMap (UInt256.ofNat asset.val) ok out),
            uint256Value (callReturnCursor ptr out)])) ∧
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0
        (if optionalBoolValue evm'.accountMap (UInt256.ofNat asset.val) ok out then ⟨1153⟩ else ⟨1420⟩)
        [UInt256.ofNat spender.val, UInt256.ofNat asset.val, request, ⟨32⟩, ⟨64⟩]
        (callReturnMemory mem ptr out) aw' out evm'.accountMap k' C') := by
  obtain ⟨evm', ok, out, _, _, _, hc, hs', hout, r1⟩ :=
    constructorApproveCall asset spender (by simp) hr hbuffer hs rd
  have r2 := metaMorphoV1_1Creation_block_1127 (by simp) (by native_decide) r1
  rcases constructorCallReturnBuffer (by simp) hp (by change _ < 2 ^ 256; omega)
      hfree (by native_decide) r2 with hbad | hgood
  · exact .inl ⟨optionalBoolCallBodyReverts imms asset _ ptr ok out hc (.inl hbad.1), hbad.2⟩
  · obtain ⟨hfit, _, _, _, r3⟩ := hgood
    have hout' : out.size < 2 ^ 64 := by rcases hfit with hz | ⟨h, _⟩ <;> omega
    rcases constructorOptionalBoolResult ok (by simp) hout'
        (callReturnMemory_length mem ptr out hzero)
        (fun h => callReturnMemory_word mem ptr out h (by change _ < 2 ^ 256; omega)) r3
        with hbad | hgood
    · exact .inl ⟨optionalBoolCallBodyReverts imms asset _ ptr ok out hc (.inr hbad.1), hbad.2⟩
    · obtain ⟨hv, aw4, k4, C4, r4⟩ := hgood
      exact .inr ⟨evm', ok, out, aw4, k4, C4, hs', hfit,
        optionalBoolCallBodyReturns imms asset _ ptr ok out hc hfit hv, r4⟩

end Benchmarks.Morpho.MetaMorphoV1_1
