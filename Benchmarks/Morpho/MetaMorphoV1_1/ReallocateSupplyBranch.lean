import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateSupplyAmountRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateSupplyCapSource
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateSupplyCapRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateSupplySimulation
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateSupplyFinishSource
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateSupplyFinishRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.MappingScratchMemory

/-! The whole supply branch, including its zero-amount continue and strict-call failures. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem reallocateSupplyBranch {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {values : List Value} {mem row : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr allocation params assets shares amount withdrawn id offset i len supplied saved : UInt256}
    {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 24 ≤ 1024)
    (hl : ReallocateLocals v frame values i supplied withdrawn ptr)
    (hrow : frame.locals.get? "allocation" = some (reallocateAllocationValue row))
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hassets : frame.locals.get? "supplyAssets" = some (uint256Value assets))
    (halloc : memLoad allocation mem = params)
    (halloclo : 96 ≤ allocation.toNat) (hallocspan : allocation.toNat + 32 ≤ ptr.toNat)
    (hallocmem : allocation.toNat + 32 ≤ mem.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hptr : ptr.toNat < 2 ^ 64)
    (hparamslo : 96 ≤ params.toNat) (hspan : params.toNat + 160 ≤ ptr.toNat)
    (hmem : params.toNat + 160 ≤ mem.size) (hloads : MarketParamsLoads mem params (marketParamsData row))
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨6450⟩
      ([calldataWord row 160, assets, shares, allocation, allocation + ⟨32⟩,
        amount, withdrawn, id, offset, i, len, supplied, saved] ++ R) mem aw rdata σ k C) :
    (ExecBlock config frame evm reallocateSupplyBody .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (ExecBlock config frame evm reallocateSupplyBody .staticViolation ∧ RDstatic (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (mem' out : ByteArray) (aw' supplied' ptr' : UInt256) (k' C' : Nat),
      SourceState s0 I evm'.accountMap evm' ∧
      ReallocateLocals v frame' values i supplied' withdrawn ptr' ∧
      (ExecBlock config frame evm reallocateSupplyBody (.ok frame' evm') ∨
        ExecBlock config frame evm reallocateSupplyBody (.continue frame' evm')) ∧
      memLoad ⟨64⟩ mem' = ptr' ∧ 96 ≤ ptr'.toNat ∧ ptr'.toNat < 2 ^ 64 ∧
      MemoryPrefix mem mem' ptr.toNat ∧
      RD (deployedRuntime v) I g s0 ⟨6380⟩
        ([i, ⟨1⟩, offset, withdrawn, len, supplied', saved] ++ R)
        mem' aw' out evm'.accountMap k' C' := by
  let target := calldataWord row 160
  let suppliedAmount := reallocateSupplyAmount target assets supplied withdrawn
  let frame1 := reallocateSupplyAmountFrame frame target assets supplied withdrawn
  have hl1 : ReallocateLocals v frame1 values i supplied withdrawn ptr := hl.supplyAmount target assets
  have hr1 : frame1.locals.get? "allocation" = some (reallocateAllocationValue row) := by
    rw [reallocateSupplyAmountFrame_preserves _ _ _ _ _ _ (by decide) (by decide) (by decide)]; exact hrow
  have hi1 : frame1.locals.get? "id" = some (wordBytes32Value id) := by
    rw [reallocateSupplyAmountFrame_preserves _ _ _ _ _ _ (by decide) (by decide) (by decide)]; exact hid
  have ha1 : frame1.locals.get? "supplyAssets" = some (uint256Value assets) := by
    rw [reallocateSupplyAmountFrame_preserves _ _ _ _ _ _ (by decide) (by decide) (by decide)]; exact hassets
  have hm1 : frame1.locals.get? "suppliedAssets" = some (uint256Value suppliedAmount) := store_get_self _ _ _
  have hsetup := reallocateSupplyAmountSource (evm := evm) hl.contract hl.supplied hl.withdrawn hassets hrow
  obtain ⟨aw1, k1, C1, h1⟩ := reallocateSupplyAmountRuntime v (by omega) rd
  by_cases hz : suppliedAmount = ⟨0⟩
  · obtain ⟨aw2, k2, C2, h2⟩ := reallocateSupplyContinueRuntime v (by omega) hz h1
    have hcontinue := reallocateSupplyContinueSource (evm := evm) hm1 hz
    refine .inr (.inr ⟨evm, frame1, mem, rdata, aw2, supplied, ptr, k2, C2, ?_, hl1,
      .inr (execBlockAppendOk hsetup hcontinue), hfree, hlo, hptr, MemoryPrefix.refl _ _, ?_⟩)
    · exact { hs with accounts := rfl }
    · simpa only [hs.accounts] using h2
  have hnonzero := reallocateSupplyNonzeroSource (evm := evm) hm1 hz
  have hcapEq : marketRemovalCap evm id = maxDepositCapWord I σ id := by
    unfold marketRemovalCap marketRemovalConfigWord maxDepositCapWord
    rw [hs.storageRead]
  rcases reallocateSupplyCapRuntime v (by dsimp only [List.append, List.length_cons]; omega) hz h1 with
    ⟨hbad, hrev⟩ | ⟨hcap, aw2, k2, C2, h2⟩
  · have hsource := reallocateSupplyCapRevert (evm := evm) hl1.contract hl1.config hi1 ha1 hm1
      (by rwa [hcapEq])
    exact .inl ⟨execBlockAppendOk hsetup (hnonzero.run hsource), hrev⟩
  have hcapSource := reallocateSupplyCapSource (evm := evm) hl1.contract hl1.config hi1 ha1 hm1
    (by rwa [hcapEq])
  let frame2 := reallocateSupplyCapFrame frame1 (marketRemovalCap evm id)
  have hl2 : ReallocateLocals v frame2 values i supplied withdrawn ptr := hl1.supplyCap _
  have hr2 : frame2.locals.get? "allocation" = some (reallocateAllocationValue row) := by
    dsimp only [frame2, reallocateSupplyCapFrame]
    rw [store_get_ne _ _ (by decide)]; exact hr1
  have hi2 : frame2.locals.get? "id" = some (wordBytes32Value id) := by
    dsimp only [frame2, reallocateSupplyCapFrame]
    rw [store_get_ne _ _ (by decide)]; exact hi1
  have hm2 : frame2.locals.get? "suppliedAssets" = some (uint256Value suppliedAmount) := by
    dsimp only [frame2, reallocateSupplyCapFrame]
    rw [store_get_ne _ _ (by decide)]; exact hm1
  have hprefix : ABlock config evm frame reallocateSupplyBody frame2 (reallocateSupplyBody.drop 6) := by
    constructor
    intro result htail
    exact execBlockAppendOk hsetup (hnonzero.run (execBlockAppendOk hcapSource htail))
  have hp := twoWordHashMem_prefix mem id ⟨13⟩ ptr.toNat
  have hm : 96 ≤ mem.size := by omega
  have hf2 : memLoad ⟨64⟩ (twoWordHashMem id ⟨13⟩ mem) = ptr := (twoWordHashMem_free _ _ hm).trans hfree
  have hal2 : memLoad allocation (twoWordHashMem id ⟨13⟩ mem) = params := by
    have h := hp.load_preserved halloclo hallocspan hallocmem allocation.val.isLt
    rw [u256_ofNat_toNat] at h
    exact h.trans halloc
  have hloads2 := hloads.prefix hp hparamslo hmem hspan (by change _ < 2 ^ 256; omega)
  rcases reallocateSupplySimulation v (marketParamsData row)
      (by dsimp only [List.append, List.length_cons]; omega) hs hal2 hf2 hptr hparamslo hspan
      (le_trans hmem hp.size) hloads2 h2 with
    ⟨evm', ok, out, hcall, hhi, hbad, hrev⟩ |
      ⟨evm', out, mem3, aw3, k3, C3, hcall, hs3, hhi, hlong, hfit, hfree3, hp3, h3⟩
  · have hsource := reallocateSupplyCallSourceRevert (evm := evm) (evm' := evm') hl2 hr2 hm2
      (by simpa only [hs.env] using hcall) hhi hbad
    exact .inl ⟨hprefix.run (execBlockAppendReverted hsource), hrev⟩
  have hsource := reallocateSupplyCallSource (evm := evm) (evm' := evm') hl2 hr2 hm2
    (by simpa only [hs.env] using hcall) hhi hlong hfit
  let frame3 := strictPairCallFrame frame2 "__c9" ptr out
  have hl3 : ReallocateLocals v frame3 values i supplied withdrawn (nextCursor ptr ⟨64⟩) :=
    hl2.strictPair "__c9" out (by decide)
  have hret : frame3.locals.get? "__c9" = some (strictPairCallValue out) :=
    strictPairCallFrame_value _ _ _ _ (by decide)
  have hi3 : frame3.locals.get? "id" = some (wordBytes32Value id) := by
    rw [strictPairCallFrame_preserves _ _ _ _ _ (by decide) (by decide)]; exact hi2
  have hm3 : frame3.locals.get? "suppliedAssets" = some (uint256Value suppliedAmount) := by
    rw [strictPairCallFrame_preserves _ _ _ _ _ (by decide) (by decide)]; exact hm2
  cases hperm : I.perm with
  | false =>
      have hstatic := reallocateSupplyFinishStatic hl3.contract hret hi3 hm3 (by rw [hs3.env]; exact hperm)
      exact .inr (.inl ⟨hprefix.run (execBlockAppendOk hsource hstatic),
        reallocateSupplyFinishRuntimeStatic v (by omega) hperm h3⟩)
  | true =>
      rcases reallocateSupplyFinishRuntime v (by omega) hperm hfree3 hfit.1 h3 with
        ⟨hover, hrev⟩ | ⟨hfitAdd, aw4, k4, C4, h4⟩
      · have hfinish := reallocateSupplyFinishRevert (evm := evm') hl3.contract hret hl3.supplied hi3 hm3 hover
        exact .inl ⟨hprefix.run (execBlockAppendOk hsource hfinish), hrev⟩
      have hfinish := reallocateSupplyFinishSource (evm := evm') hl3.contract hret hl3.supplied hi3 hm3 hfitAdd
      let frame4 := reallocateSupplyFinishFrame frame3 out evm'.executionEnv.source supplied suppliedAmount
      have hmem3 : 96 ≤ mem3.size := le_trans hm (hp.trans hp3).size
      have hlo3 : 96 ≤ (nextCursor ptr ⟨64⟩).toNat := le_trans hlo hfit.2
      exact .inr (.inr ⟨evm', frame4, reallocateEventMemory mem3 (nextCursor ptr ⟨64⟩)
          suppliedAmount (calldataWord out 32), out, aw4, supplied + suppliedAmount, nextCursor ptr ⟨64⟩,
        k4, C4, hs3, hl3.supplyFinish out evm'.executionEnv.source suppliedAmount,
        .inl (hprefix.run (execBlockAppendOk hsource hfinish)),
        (reallocateEventMemory_free hmem3 hlo3).trans hfree3, hlo3, hfit.1,
        (hp.trans hp3).trans ((reallocateEventMemory_prefix _ _ _ _).mono hfit.2), h4⟩)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
