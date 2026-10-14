import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateRowPrefix
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateRowContinuation

/-! One complete reallocation iteration, before the loop-counter increment. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem reallocateIterationSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {values : List Value} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr remaining base withdrawn offset i len supplied saved : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 29 ≤ 1024)
    (hl : ReallocateLocals v frame values i supplied withdrawn ptr)
    (hvalue : values[i.toNat]? = some
      (if MarketParamsChecks (reallocateRowBytes I.calldata (base.toNat + 36)) then
        reallocateRowValue (reallocateRowBytes I.calldata (base.toNat + 36))
        else ABI.Solc08Calldata.decodeFailure))
    (hin : base.toNat + 228 ≤ I.calldata.size) (hbase : base.toNat + 228 < UInt256.size)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hremaining : 160 ≤ remaining.toNat) (hremhi : remaining.toNat < 2 ^ 255)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨5985⟩
      ([remaining, withdrawn, base, offset, i, len, supplied, saved] ++ R) mem aw rdata σ k C) :
    (ExecBlock config frame evm reallocateIteration .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (ExecBlock config frame evm reallocateIteration .staticViolation ∧ RDstatic (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (mem' out : ByteArray)
      (aw' supplied' withdrawn' ptr' : UInt256) (k' C' : Nat),
      SourceState s0 I evm'.accountMap evm' ∧ ReallocateLocals v frame' values i supplied' withdrawn' ptr' ∧
      (ExecBlock config frame evm reallocateIteration (.ok frame' evm') ∨
        ExecBlock config frame evm reallocateIteration (.continue frame' evm')) ∧
      memLoad ⟨64⟩ mem' = ptr' ∧ 96 ≤ ptr'.toNat ∧ ptr'.toNat < 2 ^ 64 ∧
      96 ≤ mem'.size ∧
      RD (deployedRuntime v) I g s0 ⟨6380⟩
        ([i, ⟨1⟩, offset, withdrawn', len, supplied', saved] ++ R)
        mem' aw' out evm'.accountMap k' C' := by
  rcases reallocateRowPrefixSimulation v (by dsimp only [List.append, List.length_cons]; omega)
      hl.contract hl.config hl.cursor hl.input hl.index hvalue hin hbase hfree hremaining hremhi hs rd with
    ⟨hbad, hrev⟩ | ⟨hfit, hchecks, hprefix, aw1, k1, C1, h1⟩
  · exact .inl ⟨execBlockAppendReverted hbad, hrev⟩
  let row := reallocateRowBytes I.calldata (base.toNat + 36)
  let frame1 := reallocateIdentifiedFrame (reallocateReserveFrame frame ptr) row
  let mem1 := reallocateRowFinalMem mem ptr row
  have hl1 : ReallocateLocals v frame1 values i supplied withdrawn (nextCursor ptr ⟨224⟩) :=
    hl.reserve.identified row
  have hr1 : frame1.locals.get? "allocation" = some (reallocateAllocationValue row) := by
    simp only [frame1, reallocateIdentifiedFrame, reallocateRowFrame,
      store_get_ne _ _ (by decide : ("id" == "allocation") = false), store_get_self]
  have hi1 : frame1.locals.get? "id" = some (wordBytes32Value (marketParamsData row).id) :=
    store_get_self _ _ _
  obtain ⟨hp64, hp224, hupper⟩ := reallocateRowReservationBounds hfit
  have hm : mem1.size = max mem.size (ptr.toNat + 224) := reallocateRowFinalMem_size hlo hfit
  have hmlo : 96 ≤ mem1.size := by omega
  dsimp only [mem1] at hm
  rcases reallocateRowContinuationSimulation v hstack hl1 hr1 hi1 hcalldata
      (reallocateRowFinalMem_params hlo hfit) (reallocateRowFinalMem_assets hlo hfit)
      hlo (by omega) (by omega) (reallocateRowFinalMem_free hlo hfit) (by omega) hfit.1
      (by omega) (by omega) (by omega) (reallocateRowFinalMem_loads hlo hfit hchecks) hs h1 with
    ⟨hbad, hrev⟩ | ⟨hstatic, hsrev⟩ |
      ⟨evm2, frame2, mem2, out2, aw2, supplied2, withdrawn2, ptr2, k2, C2, hs2, hl2,
        hsource, hf2, hlo2, hhi2, hp2, h2⟩
  · exact .inl ⟨execBlockAppendOk hprefix hbad, hrev⟩
  · exact .inr (.inl ⟨execBlockAppendOk hprefix hstatic, hsrev⟩)
  · refine .inr (.inr ⟨evm2, frame2, mem2, out2, aw2, supplied2, withdrawn2, ptr2,
      k2, C2, hs2, hl2, ?_, hf2, hlo2, hhi2, le_trans hmlo hp2.size, h2⟩)
    exact hsource.elim (fun h ↦ .inl (execBlockAppendOk hprefix h))
      (fun h ↦ .inr (execBlockAppendOk hprefix h))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
