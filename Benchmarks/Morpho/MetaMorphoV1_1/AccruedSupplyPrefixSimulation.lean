import Benchmarks.Morpho.MetaMorphoV1_1.AccruedSupplySetup
import Benchmarks.Morpho.MetaMorphoV1_1.AccruedSupplyAccrueCall
import Benchmarks.Morpho.MetaMorphoV1_1.AccruedSupplyMarketRead
import Benchmarks.Morpho.MetaMorphoV1_1.AccruedSupplySource

/-! Composition through initial allocation, accrual, and the decoded market. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

structure AccruedSupplyLocals (v : MetaMorphoV1_1Immutables) (frame : Frame)
    (id cursor : UInt256) (market : ByteArray) : Prop where
  contract : frame.contract = contract
  imms : frame.immutables = immStore v
  id : frame.locals.get? "id" = some (wordBytes32Value id)
  cursor : frame.locals.get? cursorName = some (uint256Value cursor)
  market : frame.locals.get? "market" = some (marketValue market)
  assets : frame.locals.get? "assets" = some (.int 0)
  shares : frame.locals.get? "shares" = some (.int 0)

structure AccruedSupplyMarketResult (before : ByteArray) (initial : UInt256) (out : ByteArray) where
  memory : ByteArray
  cursor : UInt256
  marketPtr : UInt256
  free : memLoad ⟨64⟩ memory = cursor
  cursorLower : initial.toNat ≤ cursor.toNat
  lower : 96 ≤ cursor.toNat
  upper : cursor.toNat < 2 ^ 64
  size : cursor.toNat ≤ memory.size
  marketLower : 96 ≤ marketPtr.toNat
  marketSpan : marketPtr.toNat + 192 ≤ cursor.toNat
  fields : ∀ i, i < 6 → memLoad (marketPtr + UInt256.ofNat (32 * i)) memory =
    calldataWord out (32 * i)
  preserves : MemoryPrefix before memory initial.toNat

set_option maxRecDepth 2000 in
theorem accruedSupplyPrefixSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params id : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 15 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hparamslo : 96 ≤ params.toNat) (hspan : params.toNat + 160 ≤ ptr.toNat)
    (hmem : params.toNat + 160 ≤ mem.size) (hloads : MarketParamsLoads mem params p)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨14951⟩ (params :: id :: R) mem aw rdata σ k C) :
    (ExecFuncBody config (accruedSupplyFrame (immStore v) p id ptr) evm
      allocatedAccruedSupplyBalanceFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (market : ByteArray)
      (result : AccruedSupplyMarketResult mem ptr market) (aw' : UInt256) (k' C' : Nat),
      SourceState s0 I evm'.accountMap evm' ∧ MarketChecks market ∧
      AccruedSupplyLocals v frame' id result.cursor market ∧
      (∀ outcome, ExecBlock config frame' evm' (accruedSupplyShares ++ accruedSupplyTail) outcome →
        ExecBlock config (accruedSupplyFrame (immStore v) p id ptr) evm
          allocatedAccruedSupplyBalanceFunction.body outcome) ∧
      RD (deployedRuntime v) I g s0 ⟨15141⟩
        (⟨15158⟩ :: UInt256.ofNat v.MORPHO.toNat :: id :: result.marketPtr :: R)
        result.memory aw' market evm'.accountMap k' C' := by
  rcases accruedSupplyInitial v (by omega) hfree rd with
    ⟨hbad, hrev⟩ | ⟨hfit, hz, hrev⟩ | ⟨hfit, hz, aw1, k1, C1, h1⟩
  · refine .inl ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    rw [allocatedAccruedSupplyBalanceFunction_body]
    exact accruedSupplyInitialSourceReverts evm _ p id ptr hbad _
  · refine .inl ⟨ExecFuncBody.execBlockRevert ?_, hrev⟩
    rw [allocatedAccruedSupplyBalanceFunction_body]
    apply (accruedSupplyInitialSource evm v p id ptr hfit _).run
    apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
    have hg := supplyMorphoCodeSource
      (frame := accruedSupplyGuardFrame (immStore v) v.MORPHO p id ptr) (evm := evm) v rfl
    simpa only [← hs.accounts, hz, ne_eq, not_true_eq_false, decide_false] using hg
  let frame1 := accruedSupplyGuardFrame (immStore v) v.MORPHO p id ptr
  let frame2 := accruedSupplyAccruedFrame frame1
  let ptr1 := nextCursor ptr ⟨192⟩
  let mem1 := accruedSupplyInitialMem mem ptr
  let mem2 := morphoAccrueReturnMem mem1 ptr1 p
  have hpre : ∀ outcome, ExecBlock config frame1 evm
      (accruedSupplyGuard :: accruedSupplyAccrue :: accruedSupplyMarket ++
        accruedSupplyShares ++ accruedSupplyTail) outcome →
      ExecBlock config (accruedSupplyFrame (immStore v) p id ptr) evm
        allocatedAccruedSupplyBalanceFunction.body outcome := by
    intro outcome htail
    rw [allocatedAccruedSupplyBalanceFunction_body]
    exact (accruedSupplyInitialSource evm v p id ptr hfit _).run htail
  have hguard : ExecStmt config frame1 evm accruedSupplyGuard (.ok frame1 evm) := by
    apply ExecStmt.requireTrue
    have hg := supplyMorphoCodeSource (frame := frame1) (evm := evm) v rfl
    rw [← hs.accounts, decide_eq_true hz] at hg
    exact hg
  have hm : frame1.locals.get? "morphoTarget" = some (.address v.MORPHO) := by
    simp [frame1, accruedSupplyGuardFrame, Std.HashMap.getElem_insert]
  have hp : frame1.locals.get? "marketParams" = some p.value := by
    simp [frame1, accruedSupplyGuardFrame, accruedSupplyFrame, cursorName, Std.HashMap.getElem_insert]
  have hn1 : ptr1.toNat = ptr.toNat + 192 := by
    exact uadd_word_ofNat_toNat ptr 192 (lt_trans
      ((allocationFits_aligned ptr ⟨192⟩ (by decide +kernel)).mp hfit) (by decide))
  have hpres1 := accruedSupplyInitialMem_prefix mem ptr
  have hloads1 := hloads.prefix hpres1 hparamslo hmem hspan
    (lt_of_le_of_lt hspan ptr.val.isLt)
  obtain ⟨gasArg, aw2, k2, C2, h2⟩ := accruedSupplyReachAccrue v p
    (by simp only [List.length_cons]; omega) (accruedSupplyInitialMem_free mem ptr hlo)
    hfit.1 hparamslo (by rw [hn1]; omega) (by have hm := hpres1.size; omega) hloads1 h1
  have ha : AccountAddress.ofUInt256 (UInt256.ofNat v.MORPHO.toNat) = v.MORPHO := by
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    exact accountAddress_of_word_val _
  rcases accruedSupplyAccrueCall v p (UInt256.ofNat v.MORPHO.toNat)
      (by omega) hs hfit.1 h2 with
    ⟨evm2, out2, hcall2, hrev⟩ | ⟨evm2, out2, aw3, k3, C3, hcall2, hs2, h3⟩
  · rw [ha] at hcall2
    exact .inl ⟨ExecFuncBody.execBlockRevert (hpre _
      (ExecBlock.consNormal hguard (ExecBlock.consRevert
        (accruedSupplyAccrueReverts hm hp hcall2)))), hrev⟩
  rw [ha] at hcall2
  have haccrue := accruedSupplyAccrueSuccess hm hp hcall2
  have hm2 : frame2.locals.get? "morphoTarget" = some (.address v.MORPHO) := by
    simp only [frame2, accruedSupplyAccruedFrame,
      store_get_ne _ _ (by decide : ("__c0" == "morphoTarget") = false), hm]
  have hi2 : frame2.locals.get? "id" = some (wordBytes32Value id) := by
    simp [frame2, accruedSupplyAccruedFrame, frame1, accruedSupplyGuardFrame,
      accruedSupplyFrame, cursorName, Std.HashMap.getElem_insert]
  have hc2 : frame2.locals.get? cursorName = some (uint256Value ptr1) := by
    simp [frame2, accruedSupplyAccruedFrame, frame1, accruedSupplyGuardFrame,
      cursorName, Std.HashMap.getElem_insert, ptr1]
  have hold2 : frame2.locals.get? "market" = some accruedSupplyZeroMarket := by
    simp [frame2, accruedSupplyAccruedFrame, frame1, accruedSupplyGuardFrame, Std.HashMap.getElem_insert]
  rcases accruedSupplyMarketRead v hstack (morphoAccrueReturnMem_free mem1 ptr1 p)
      (by rw [hn1]; omega) hfit.1 hs2 h3 with
    ⟨evm3, market, ok, hcall3, hbad, hrev⟩ |
    ⟨evm3, market, aw4, k4, C4, hcall3, hs3, hmarket, hhi, hfit3,
      hfree3, hsize3, hfields3, hprefix3, h4⟩
  · rw [ha] at hcall3
    refine .inl ⟨ExecFuncBody.execBlockRevert (hpre _
      (ExecBlock.consNormal hguard (ExecBlock.consNormal haccrue ?_))), hrev⟩
    exact accruedSupplyMarketReverts (frame := frame2) rfl hm2 hi2 hc2 hcall3
      (lt_trans (marketReturnSize hcall3) (by decide)) hbad _
  rw [ha] at hcall3
  let frame3 := accruedSupplyMarketFrame frame2 ptr1 market
  have hbound3 : ptr1.toNat + 384 < 2 ^ 64 :=
    (allocationFits_aligned ptr1 ⟨384⟩ (by decide +kernel)).mp hfit3
  have hn3 : (nextCursor ptr1 ⟨384⟩).toNat = ptr1.toNat + 384 :=
    uadd_word_ofNat_toNat ptr1 384 (lt_trans hbound3 (by decide))
  have hnmarket : (nextCursor ptr1 ⟨192⟩).toNat = ptr1.toNat + 192 :=
    uadd_word_ofNat_toNat ptr1 192 (by change _ < 2 ^ 256; omega)
  let result : AccruedSupplyMarketResult mem ptr market :=
    { memory := marketReadMemory mem2 ptr1 id market
      cursor := nextCursor ptr1 ⟨384⟩
      marketPtr := nextCursor ptr1 ⟨192⟩
      free := hfree3
      cursorLower := by rw [hn3, hn1]; omega
      lower := by rw [hn3, hn1]; omega
      upper := hfit3.1
      size := hsize3
      marketLower := by rw [hnmarket, hn1]; omega
      marketSpan := by rw [hnmarket, hn3]
      fields := hfields3
      preserves := hpres1.trans (((morphoAccrueReturnMem_prefix mem1 ptr1 p).trans
        hprefix3).mono (by rw [hn1]; omega)) }
  refine .inr ⟨evm3, frame3, market, result, aw4, k4, C4, hs3, hmarket, ?_, ?_, h4⟩
  · constructor
    · rfl
    · rfl
    all_goals simp [frame3, accruedSupplyMarketFrame, accruedSupplyDecodedFrame,
      frame2, accruedSupplyAccruedFrame, frame1, accruedSupplyGuardFrame, accruedSupplyFrame,
      cursorName, Std.HashMap.getElem_insert, result, ptr1]
  · intro outcome htail
    apply hpre
    apply ExecBlock.consNormal hguard
    apply ExecBlock.consNormal haccrue
    exact accruedSupplyMarketPrefix (frame := frame2) rfl hm2 hi2 hc2 hold2 hcall3
      hmarket hhi hfit3 htail

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
