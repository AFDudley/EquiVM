import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateAmountRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateWithdrawSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateWithdrawFinishRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateWithdrawFinishSource

/-! Complete simulation of the strict withdrawal branch of a reallocation row. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem reallocateWithdrawBranch {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {values : List Value} {mem row : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr allocation params assets shares amount withdrawn id offset i len supplied saved : UInt256}
    {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 20 ≤ 1024)
    (hl : ReallocateLocals v frame values i supplied withdrawn ptr)
    (hrow : frame.locals.get? "allocation" = some (reallocateAllocationValue row))
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hshares : frame.locals.get? "supplyShares" = some (uint256Value shares))
    (hamount : frame.locals.get? "withdrawn" = some (uint256Value amount))
    (halloc : memLoad allocation mem = params)
    (hasset : memLoad (allocation + ⟨32⟩) mem = calldataWord row 160)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hptr : ptr.toNat < 2 ^ 64)
    (hparamslo : 96 ≤ params.toNat) (hspan : params.toNat + 160 ≤ ptr.toNat)
    (hmem : params.toNat + 160 ≤ mem.size) (hloads : MarketParamsLoads mem params (marketParamsData row))
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨6182⟩
      ([calldataWord row 160, assets, shares, allocation, allocation + ⟨32⟩,
        amount, withdrawn, id, offset, i, len, supplied, saved] ++ R) mem aw rdata σ k C) :
    (ExecBlock config frame evm reallocateWithdrawBody .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (ExecBlock config frame evm reallocateWithdrawBody .staticViolation ∧ RDstatic (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (mem' out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      SourceState s0 I evm'.accountMap evm' ∧
      ReallocateLocals v frame' values i supplied (withdrawn + calldataWord out 0) (nextCursor ptr ⟨64⟩) ∧
      ExecBlock config frame evm reallocateWithdrawBody (.ok frame' evm') ∧
      memLoad ⟨64⟩ mem' = nextCursor ptr ⟨64⟩ ∧
      96 ≤ (nextCursor ptr ⟨64⟩).toNat ∧ (nextCursor ptr ⟨64⟩).toNat < 2 ^ 64 ∧
      MemoryPrefix mem mem' ptr.toNat ∧
      RD (deployedRuntime v) I g s0 ⟨6380⟩
        ([i, ⟨1⟩, offset, withdrawn + calldataWord out 0, len, supplied, saved] ++ R)
        mem' aw' out evm'.accountMap k' C' := by
  let target := calldataWord row 160
  let frame1 := reallocateWithdrawSetupFrame frame target shares
  have hl1 : ReallocateLocals v frame1 values i supplied withdrawn ptr := hl.withdrawSetup target shares
  have hr1 : frame1.locals.get? "allocation" = some (reallocateAllocationValue row) := by
    rw [reallocateWithdrawSetupFrame_preserves _ _ _ _ (by decide) (by decide)]; exact hrow
  have hi1 : frame1.locals.get? "id" = some (wordBytes32Value id) := by
    rw [reallocateWithdrawSetupFrame_preserves _ _ _ _ (by decide) (by decide)]; exact hid
  have hw1 := reallocateWithdrawSetupFrame_amount target shares amount hamount
  have hsh1 := reallocateWithdrawSetupFrame_shares frame target shares
  have hsetup := reallocateWithdrawSetupSource (evm := evm) hrow hshares hamount
  obtain ⟨scratch, aw1, k1, C1, h1⟩ := reallocateWithdrawSetupRuntime v (by omega) hasset rd
  rcases reallocateWithdrawSimulation v (marketParamsData row)
      (by dsimp only [List.append, List.length_cons]; omega) hs halloc hfree hptr hparamslo hspan hmem hloads h1 with
    ⟨evm', ok, out, hcall, hhi, hbad, hrev⟩ |
      ⟨evm', out, mem2, aw2, k2, C2, hcall, hs2, hhi, hlong, hfit, hfree2, hp2, h2⟩
  · have hsource := reallocateWithdrawCallSourceRevert (evm := evm) (evm' := evm') hl1 hr1 hw1 hsh1
      (by simpa only [hs.env] using hcall) hhi hbad
    exact .inl ⟨execBlockAppendOk hsetup (execBlockAppendReverted hsource), hrev⟩
  have hsource := reallocateWithdrawCallSource (evm := evm) (evm' := evm') hl1 hr1 hw1 hsh1
    (by simpa only [hs.env] using hcall) hhi hlong hfit
  let frame2 := strictPairCallFrame frame1 "__c5" ptr out
  have hl2 : ReallocateLocals v frame2 values i supplied withdrawn (nextCursor ptr ⟨64⟩) :=
    hl1.strictPair "__c5" out (by decide)
  have hret : frame2.locals.get? "__c5" = some (strictPairCallValue out) :=
    strictPairCallFrame_value _ _ _ _ (by decide)
  have hid2 : frame2.locals.get? "id" = some (wordBytes32Value id) := by
    rw [strictPairCallFrame_preserves _ _ _ _ _ (by decide) (by decide)]; exact hi1
  cases hperm : I.perm with
  | false =>
      have hstatic := reallocateWithdrawFinishStatic hl2.contract hret hid2 (by rw [hs2.env]; exact hperm)
      exact .inr (.inl ⟨execBlockAppendOk hsetup (execBlockAppendOk hsource hstatic),
        reallocateWithdrawFinishRuntimeStatic v (by omega) hperm h2⟩)
  | true =>
      rcases reallocateWithdrawFinishRuntime v (by omega) hperm hfree2 hfit.1 h2 with
        ⟨hover, hrev⟩ | ⟨hfitAdd, aw3, k3, C3, h3⟩
      · have hfinish := reallocateWithdrawFinishRevert (evm := evm') hl2.contract hret hl2.withdrawn hid2 hover
        exact .inl ⟨execBlockAppendOk hsetup (execBlockAppendOk hsource hfinish), hrev⟩
      have hfinish := reallocateWithdrawFinishSource (evm := evm') hl2.contract hret hl2.withdrawn hid2 hfitAdd
      let frame3 := reallocateWithdrawFinishFrame frame2 out evm'.executionEnv.source withdrawn
      have hm2 : 96 ≤ mem2.size := le_trans (by omega) hp2.size
      have hlo2 : 96 ≤ (nextCursor ptr ⟨64⟩).toNat := le_trans hlo hfit.2
      exact .inr (.inr ⟨evm', frame3, reallocateEventMemory mem2 (nextCursor ptr ⟨64⟩)
          (calldataWord out 0) (calldataWord out 32), out, aw3, k3, C3, hs2,
        hl2.withdrawFinish out evm'.executionEnv.source,
        execBlockAppendOk hsetup (execBlockAppendOk hsource hfinish),
        (reallocateEventMemory_free hm2 hlo2).trans hfree2, hlo2, hfit.1,
        hp2.trans ((reallocateEventMemory_prefix _ _ _ _).mono hfit.2), h3⟩)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
