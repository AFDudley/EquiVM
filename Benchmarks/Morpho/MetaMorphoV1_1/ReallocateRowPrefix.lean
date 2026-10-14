import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateRowSource
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateReserveSource
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateRowEnabled
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateRowHeap

/-! Reallocation-row allocation, deferred decode, and enabled-market simulation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
attribute [local irreducible] contract

set_option maxRecDepth 2000 in
theorem reallocateRowPrefixSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr remaining withdrawn base : UInt256} {R : List UInt256}
    {frame : Frame} {values : List Value} {i : Nat}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (hc : frame.contract = contract) (hconfig : frame.locals.get? "config" = none)
    (hcursor : frame.locals.get? cursorName = some (uint256Value ptr))
    (hinput : frame.locals.get? "allocations" = some (.array values))
    (hindex : frame.locals.get? "i" = some (.int (Int.ofNat i)))
    (hvalue : values[i]? = some
      (if MarketParamsChecks (reallocateRowBytes I.calldata (base.toNat + 36)) then
        reallocateRowValue (reallocateRowBytes I.calldata (base.toNat + 36))
        else ABI.Solc08Calldata.decodeFailure))
    (hin : base.toNat + 228 ≤ I.calldata.size) (hbase : base.toNat + 228 < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr)
    (hlo : 160 ≤ remaining.toNat) (hhi : remaining.toNat < 2 ^ 255)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨5985⟩ (remaining :: withdrawn :: base :: R)
      mem aw rdata σ k C) :
    (ExecBlock config frame evm reallocateRowPrefix .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (allocationFits ptr ⟨224⟩ ∧ MarketParamsChecks (reallocateRowBytes I.calldata (base.toNat + 36)) ∧
      ExecBlock config frame evm reallocateRowPrefix
        (.ok (reallocateIdentifiedFrame (reallocateReserveFrame frame ptr)
          (reallocateRowBytes I.calldata (base.toNat + 36))) evm) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨6152⟩
        ((ptr + ⟨32⟩) :: ptr :: withdrawn ::
          (marketParamsData (reallocateRowBytes I.calldata (base.toNat + 36))).id :: R)
        (reallocateRowFinalMem mem ptr (reallocateRowBytes I.calldata (base.toNat + 36)))
        aw' rdata σ k' C') := by
  let row := reallocateRowBytes I.calldata (base.toNat + 36)
  rcases reallocateRowAllocation v hstack hfree hlo hhi rd with
    ⟨hbad, hrev⟩ | ⟨hfit, aw1, k1, C1, h1⟩
  · exact .inl ⟨execBlockAppendReverted
      (execBlockAppendReverted (reallocateReserveRevert hc hcursor hbad)), hrev⟩
  have hreserve := reallocateReserveSource (evm := evm) hc hcursor hfit
  have ha : (reallocateReserveFrame frame ptr).locals.get? "allocations" = some (.array values) := by
    rw [reallocateReserveFrame_preserves _ _ _ (by decide)]; exact hinput
  have hi : (reallocateReserveFrame frame ptr).locals.get? "i" = some (.int (Int.ofNat i)) := by
    rw [reallocateReserveFrame_preserves _ _ _ (by decide)]; exact hindex
  obtain ⟨hparams, _, hbound⟩ := reallocateRowReservationBounds hfit
  have hpfit : (nextCursor ptr ⟨64⟩).toNat + 160 < UInt256.size := by
    rw [hparams]
    exact lt_trans hbound (by decide)
  rcases reallocateRowFields v (by omega) hin hbase hpfit h1 with
    ⟨hbad, hrev⟩ | ⟨hchecks, aw2, k2, C2, h2⟩
  · have hv := hvalue
    rw [if_neg hbad] at hv
    exact .inl ⟨execBlockAppendReverted (execBlockAppendRevert hreserve
      (reallocateRowDeclarationRevert ha hi hv)), hrev⟩
  have hv := hvalue
  rw [if_pos hchecks] at hv
  have hdecl := reallocateRowDeclarationSource (evm := evm) ha hi hv
  have hidentified : marketRemovalEnabledWord evm (marketParamsData row).id =
      setCapEnabledWord I σ (marketParamsData row).id := by
    dsimp only [marketRemovalEnabledWord, marketRemovalConfigWord, setCapEnabledWord]
    rw [hs.storageRead]
  have hc' : (reallocateReserveFrame frame ptr).contract = contract := hc
  have hb : (reallocateReserveFrame frame ptr).locals.get? "config" = none := by
    rw [reallocateReserveFrame_preserves _ _ _ (by decide)]; exact hconfig
  rcases reallocateRowEnabled v (by omega) hin hbase (by omega) hpfit hchecks h2 with
    ⟨hbad, hrev⟩ | ⟨henabled, aw3, k3, C3, h3⟩
  · exact .inl ⟨execBlockAppendRevert (execBlockAppendOk hreserve hdecl)
      (reallocateRowIdentifyRevert hc' hb (hidentified.trans hbad)), hrev⟩
  exact .inr ⟨hfit, hchecks, execBlockAppendOk (execBlockAppendOk hreserve hdecl)
    (reallocateRowIdentifySource hc' hb (by rw [hidentified]; exact henabled)), aw3, k3, C3, h3⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
