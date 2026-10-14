import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorApproveProbe
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorApproveFallback

/-! Complete forceApprove constructor segment, including request reuse and every failure branch. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

theorem constructorForceApprove {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {mem rdata : ByteArray} {aw ptr decimals : UInt256}
    {σ : AccountMap} {k C : Nat} (a : ConstructorArgs) (imms : Store)
    (hmem : 128 ≤ mem.size) (hlo : 480 ≤ ptr.toNat) (hp : ptr.toNat < 2 ^ 64)
    (hd : decimals.toNat < 256) (hfree : memLoad ⟨64⟩ mem = ptr)
    (hzero : memLoad ⟨96⟩ mem = ⟨0⟩) (hs : SourceState s0 I σ evm)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1053⟩
      [⟨255⟩, decimals, UInt256.ofNat a.asset.val, UInt256.ofNat a.morpho.val, ⟨32⟩, ⟨64⟩]
      mem aw rdata σ k C) :
    (ExecFuncBody config (forceApproveFrame imms a.asset a.morpho constructorApprovalValue ptr)
        evm allocatedForceApproveFunction.body .reverted ∧
      RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    (∃ (evm' : State) (frame' : Frame) (mem' out : ByteArray)
        (cursor aw' x0 x1 x2 x3 : UInt256) (k' C' : Nat),
      ExecFuncBody config (forceApproveFrame imms a.asset a.morpho constructorApprovalValue ptr)
        evm allocatedForceApproveFunction.body
        (.returned frame' evm' (some [.tuple [], uint256Value cursor])) ∧
      SourceState s0 I evm'.accountMap evm' ∧
      ByteMemoryPrefix (writeWord mem 448 (constructorDecimalsOffset decimals)) mem' ptr.toNat ∧
      memLoad ⟨64⟩ mem' = cursor ∧ cursor.toNat < 2 ^ 64 ∧ ptr.toNat ≤ cursor.toNat ∧
      RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨1153⟩
        [x0, x1, x2, x3, ⟨64⟩] mem' aw' out evm'.accountMap k' C') := by
  rcases constructorApproveRequest a (by omega) (by omega) hp hd hfree rd with hbad | hgood
  · exact .inl ⟨forceApproveRevertsAllocation evm imms a.asset a.morpho _ ptr hbad.1, hbad.2⟩
  · obtain ⟨hfit, _, _, _, _, r1⟩ := hgood
    have hcursor := safeTransferCursor_bound ptr hfit
    have hb := constructorApproveMemory_buffer
      (writeWord mem 448 (constructorDecimalsOffset decimals)) ptr a.morpho constructorApprovalValue (by omega)
    have hprefix := constructorApproveMemory_bytePrefix
      (writeWord mem 448 (constructorDecimalsOffset decimals)) ptr a.morpho constructorApprovalValue
    have hbase := byteMemoryPrefix_writeWord mem 448 448 (constructorDecimalsOffset decimals) (.inl (le_refl _))
    have hm0 : 128 ≤ (writeWord mem 448 (constructorDecimalsOffset decimals)).size :=
      le_trans hmem hbase.size
    have hm1 : 128 ≤ (constructorApprovalMemory mem a ptr decimals).size :=
      le_trans hm0 hprefix.size
    have hzbase := (hbase.load ⟨96⟩ (by decide) (by decide) hmem).trans hzero
    have hz1 := (hprefix.load ⟨96⟩ (by decide) (by change 128 ≤ ptr.toNat; omega)
      hm0).trans hzbase
    have hf1 := constructorApproveMemory_free
      (writeWord mem 448 (constructorDecimalsOffset decimals)) ptr a.morpho constructorApprovalValue
    rcases constructorApproveProbe imms a.asset a.morpho hp hfit.1 hf1 hz1 hb hs r1 with hbad | hgood
    · exact .inl ⟨forceApproveRevertsProbe evm imms a.asset a.morpho _ ptr hfit hbad.1, hbad.2⟩
    · obtain ⟨evm1, ok1, out1, aw2, k2, C2, hs1, hfit1, hprobe, r2⟩ := hgood
      have hcursor1 := callReturnCursor_bound (nextCursor ptr ⟨100⟩) out1 hfit.1 hfit1
      have hp2 := callReturnMemory_bytePrefix
        (constructorApprovalMemory mem a ptr decimals) (nextCursor ptr ⟨100⟩) out1
      have hpre := hprefix.trans (hp2.mono (by omega))
      have hf2 := callReturnMemory_free (constructorApprovalMemory mem a ptr decimals)
        (nextCursor ptr ⟨100⟩) out1 (by omega) hf1
      cases hflag : optionalBoolValue evm1.accountMap (UInt256.ofNat a.asset.val) ok1 out1 with
      | true =>
          rw [hflag] at hprobe r2
          exact .inr ⟨evm1, _, _, out1, _, aw2, _, _, _, _, k2, C2,
            ExecFuncBody.execBlockRet (forceApproveProbePrefix imms a.asset a.morpho _ ptr true _
              hfit hprobe (forceApproveTailDirect evm1 imms a.asset a.morpho _ ptr _)),
            hs1, hpre, hf2, hcursor1.1, by omega, r2⟩
      | false =>
          rw [hflag] at hprobe r2
          have hloc := forceApproveReadyLocals imms a.asset a.morpho constructorApprovalValue ptr false
            (callReturnCursor (nextCursor ptr ⟨100⟩) out1)
          have hb2 := hb.preserve hp2 (by omega)
            (by rw [constructorApproveCalldata_size]; omega)
          have hz2 := (hp2.load ⟨96⟩ (by decide)
            (by change 128 ≤ (nextCursor ptr ⟨100⟩).toNat; omega)
            hm1).trans hz1
          rcases constructorApproveFallback a.asset a.morpho hloc (by omega) (by omega)
              hcursor1.1 hf2 hz2 hb2 hs1 r2 with hbad | hgood
          · exact .inl ⟨ExecFuncBody.execBlockRevert
              (forceApproveProbePrefix imms a.asset a.morpho _ ptr false _ hfit hprobe
                (forceApproveTailReverts evm1 imms a.asset a.morpho _ ptr _ hbad.1)), hbad.2⟩
          · obtain ⟨evm2, frame2, mem2, out2, cursor2, aw3, k3, C3,
              hfall, hloc2, hs2, hp3, hf3, hcb, hmono, r3⟩ := hgood
            exact .inr ⟨evm2, frame2, mem2, out2, cursor2, aw3, _, _, _, _, k3, C3,
              ExecFuncBody.execBlockRet
                (forceApproveProbePrefix imms a.asset a.morpho _ ptr false _ hfit hprobe
                  (forceApproveTailFallback imms a.asset a.morpho _ ptr _ cursor2 hfall hloc2.cursor)),
              hs2, hpre.trans (hp3.mono (by omega)), hf3, hcb, by omega, r3⟩

end Benchmarks.Morpho.MetaMorphoV1_1
