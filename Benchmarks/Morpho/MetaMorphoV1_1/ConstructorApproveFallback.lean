import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorApproveZeroRequest
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorApproveRequest
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorOptionalCall
import Benchmarks.Morpho.MetaMorphoV1_1.ForceApproveSourceTail
import Benchmarks.Morpho.MetaMorphoV1_1.SafeTransferMemory
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorZeroMemory

/-! Run both fallback approvals, preserving the original maximum request and immutable words. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

theorem constructorApproveFallback {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {frame : Frame} {mem rdata : ByteArray} {aw request ptr : UInt256}
    {σ : AccountMap} {k C : Nat} (asset spender : AccountAddress)
    (hloc : ForceApproveLocals frame asset spender constructorApprovalValue ptr)
    (hreq : 128 ≤ request.toNat) (hbelow : request.toNat + 100 ≤ ptr.toNat)
    (hp : ptr.toNat < 2 ^ 64) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hbuffer : BytesBuffer mem request (constructorApproveCalldata spender constructorApprovalValue))
    (hs : SourceState s0 I σ evm)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1420⟩
      [UInt256.ofNat spender.val, UInt256.ofNat asset.val, request, ⟨32⟩, ⟨64⟩]
      mem aw rdata σ k C) :
    (ExecBlock config frame evm forceApproveFallbackBody .reverted ∧
      RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    (∃ (evm' : State) (frame' : Frame) (mem' out : ByteArray) (cursor aw' : UInt256) (k' C' : Nat),
      ExecBlock config frame evm forceApproveFallbackBody (.ok frame' evm') ∧
      ForceApproveLocals frame' asset spender constructorApprovalValue cursor ∧
      SourceState s0 I evm'.accountMap evm' ∧ ByteMemoryPrefix mem mem' ptr.toNat ∧
      memLoad ⟨64⟩ mem' = cursor ∧ cursor.toNat < 2 ^ 64 ∧ ptr.toNat ≤ cursor.toNat ∧
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1153⟩
        [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨64⟩] mem' aw' out evm'.accountMap k' C') := by
  rcases constructorApproveZeroRequest asset spender hp hfree rd with hbad | hgood
  · exact .inl ⟨ExecBlock.consRevert (forceApproveReserveReverts hloc hbad.1), hbad.2⟩
  · obtain ⟨hfit, _, _, _, r1⟩ := hgood
    have hcursor := safeTransferCursor_bound ptr hfit
    have hreserve := forceApproveReserve (evm := evm) hloc hfit
    have hloc1 := hloc.setCursor (nextCursor ptr ⟨100⟩)
    have hp1 := constructorApproveMemory_bytePrefix mem ptr spender ⟨0⟩
    have hb1 := constructorApproveMemory_buffer mem ptr spender ⟨0⟩ (by omega)
    have hmem : 128 ≤ mem.size := by have hb := hbuffer.size; omega
    have hz1 : memLoad ⟨96⟩ (constructorApproveMemory mem ptr spender ⟨0⟩) = ⟨0⟩ :=
      (hp1.load ⟨96⟩ (by decide) (by change 128 ≤ ptr.toNat; omega) hmem).trans hzero
    have hdata1 : (constructorApproveMemory mem ptr spender ⟨0⟩).readWithPadding
        (ptr + UInt256.ofNat 32).toNat (constructorApproveCalldata spender ⟨0⟩).size =
        constructorApproveCalldata spender ⟨0⟩ := by
      rw [uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)]
      exact hb1.data
    rcases constructorOptionalCall frame.immutables asset (by simp) hs hfit.1
        (by omega) (by rw [constructorApproveCalldata_size]; decide)
        (constructorApproveMemory_free mem ptr spender ⟨0⟩) hz1 hb1.length hdata1
        (by native_decide) r1 with hbad | hgood
    · exact .inl ⟨ExecBlock.consNormal hreserve
        (ExecBlock.consRevert (forceApproveOptionalCallReverts hloc1 true hbad.1)), hbad.2⟩
    · obtain ⟨evm1, out1, _, _, _, hs1, hfit1, hcall1, hp2, hf2, r2⟩ := hgood
      have hcursor1 := callReturnCursor_bound _ out1 hfit.1 hfit1
      have hstmt1 := forceApproveOptionalCall hloc1 true hcall1
      have hloc2 := hloc1.setCursor (callReturnCursor (nextCursor ptr ⟨100⟩) out1)
      have hbuf1 := hbuffer.preserve hp1 (by omega)
        (by rw [constructorApproveCalldata_size]; omega)
      have hbuf2 := hbuf1.preserve hp2 (by omega)
        (by rw [constructorApproveCalldata_size]; omega)
      have hz2 := (hp2.load ⟨96⟩ (by decide) (by change 128 ≤ (nextCursor ptr ⟨100⟩).toNat; omega)
        (by change 128 ≤ (constructorApproveMemory mem ptr spender ⟨0⟩).size
            have hb := hp1.size; omega)).trans hz1
      have hdata2 : (callReturnMemory (constructorApproveMemory mem ptr spender ⟨0⟩)
          (nextCursor ptr ⟨100⟩) out1).readWithPadding
          (request + UInt256.ofNat 32).toNat (constructorApproveCalldata spender constructorApprovalValue).size =
          constructorApproveCalldata spender constructorApprovalValue := by
        rw [uadd_word_ofNat_toNat request 32 (by change _ < 2 ^ 256; omega)]
        exact hbuf2.data
      have r3 := metaMorphoV1_1Creation_block_1475 (by simp) (by native_decide) r2
      rcases constructorOptionalCall frame.immutables asset (by simp) hs1 hcursor1.1
          (by omega) (by rw [constructorApproveCalldata_size]; decide)
          hf2 hz2 hbuf2.length hdata2 (by native_decide) r3 with hbad | hgood
      · exact .inl ⟨ExecBlock.consNormal hreserve (ExecBlock.consNormal hstmt1
          (ExecBlock.consRevert (forceApproveOptionalCallReverts hloc2 false hbad.1))), hbad.2⟩
      · obtain ⟨evm2, out2, _, _, _, hs2, hfit2, hcall2, hp3, hf3, r4⟩ := hgood
        have hcursor2 := callReturnCursor_bound _ out2 hcursor1.1 hfit2
        have hstmt2 := forceApproveOptionalCall hloc2 false hcall2
        obtain ⟨aw5, k5, C5, r5⟩ := metaMorphoV1_1Creation_block_1480_packed
          (by simp) (by native_decide) r4
        exact .inr ⟨evm2, _, _, out2, _, aw5, k5, C5,
          ExecBlock.consNormal hreserve (ExecBlock.consNormal hstmt1
            (ExecBlock.consNormal hstmt2 ExecBlock.nil)), hloc2.setCursor _, hs2,
          hp1.trans ((hp2.mono (by omega)).trans (hp3.mono (by omega))), hf3,
          hcursor2.1, by omega, r5⟩

end Benchmarks.Morpho.MetaMorphoV1_1
