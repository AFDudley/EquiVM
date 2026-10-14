import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoReadersSource
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoAccrualSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsAllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsDecoded
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMarketSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.SupplySharesAllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_081

/-! Compose the reads and accrual preceding a supply attempt. Calls carry their actual
post-state through the simulation; no storage-invariance assumption is imposed on accrual. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem supplyMorphoReadersSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr id cap i assets : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 24 ≤ 1024)
    (hcontract : frame.contract = contract) (himms : frame.immutables = immStore v)
    (hm : frame.locals.get? "morphoTarget" = some (.address v.MORPHO))
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hcursor : frame.locals.get? cursorName = some (uint256Value ptr))
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨16116⟩
      ([id, ⟨18003⟩, cap, id, i, UInt256.ofNat v.MORPHO.toNat, assets,
        UInt256.ofNat v.MORPHO.toNat] ++ R) mem aw rdata σ k C) :
    ((∀ tail, ExecBlock config frame evm (supplyMorphoReaders ++ tail) .reverted) ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (params market mem' out : ByteArray) (src ptr1 shares cursor : UInt256),
      SourceState s0 I evm'.accountMap evm' ∧ MarketChecks market ∧
      (∀ tail result, ExecBlock config
        (supplyMorphoReadersFrame frame params ptr1 market shares cursor) evm' tail result →
        ExecBlock config frame evm (supplyMorphoReaders ++ tail) result) ∧
      memLoad ⟨64⟩ mem' = cursor ∧ 96 ≤ cursor.toNat ∧ cursor.toNat < 2 ^ 64 ∧
      cursor.toNat ≤ mem'.size ∧ ptr.toNat ≤ cursor.toNat ∧
      MemoryPrefix mem mem' ptr.toNat ∧
      96 ≤ src.toNat ∧ src.toNat + 160 ≤ cursor.toNat ∧
      MarketParamsLoads mem' src (marketParamsData params) ∧
      memLoad (nextCursor ptr1 ⟨192⟩) mem' = calldataWord market 0 ∧
      memLoad (nextCursor ptr1 ⟨192⟩ + ⟨32⟩) mem' = calldataWord market 32 ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨18119⟩
        ([shares, nextCursor ptr1 ⟨192⟩, ⟨18144⟩, cap, src, i,
          UInt256.ofNat v.MORPHO.toNat, assets, UInt256.ofNat v.MORPHO.toNat] ++ R)
        mem' aw' out evm'.accountMap k' C' := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hcontract himms hm hid hcursor
  subst c
  subst imms
  let frame : Frame := { contract := contract, locals := locals, immutables := immStore v }
  have haddr (a : AccountAddress) : AccountAddress.ofNat (UInt256.ofNat a.val).toNat = a := by
    rw [UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le a.isLt (by decide))]
    exact accountAddress_ofNat_toNat a
  have ha : AccountAddress.ofUInt256 (UInt256.ofNat v.MORPHO.toNat) = v.MORPHO := by
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    exact accountAddress_of_word_val _
  have hargs1 : evalExprs? config frame evm [.var "id", .var cursorName] =
      .ok [wordBytes32Value id, uint256Value ptr] := by
    simp only [evalExprs?, evalExpr?, frame, hid, hcursor, EvalResult.ofOption,
      bind, EvalResult.bind, pure]
  rcases marketParamsAllocationSimulation v (by simp only [List.append, List.length_cons]; omega)
      hfree hlo (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) hs rd with
    ⟨hbad, hrev⟩ | ⟨evm1, final1, params, mem1, src, ptr1, aw1, k1, C1,
      hsource1, hs1, _, hc1, hfree1, hlo1, hhi1, hmem1, hsrc, hspan, hfields,
      hmono1, hprefix1, _, h1⟩
  · exact .inl ⟨fun _ ↦ ExecBlock.consRevert (marketParamsReaderRevert hargs1 hbad), hrev⟩
  have hcall1 := marketParamsReaderCall (ret := slotsAndCursorName) hargs1 hsource1
  let frame1 := supplyMorphoParamsFrame frame params ptr1
  have hm1 : frame1.locals.get? "morphoTarget" = some (.address v.MORPHO) := by
    rw [show frame1 = cursorResultFrame frame "marketParams" _ ptr1 from rfl,
      cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact hm
  have hp1 : frame1.locals.get? "marketParams" = some (marketParamsData params).value :=
    cursorResultFrame_value _ _ _ _ (by decide)
  have hid1 : frame1.locals.get? "id" = some (wordBytes32Value id) := by
    rw [show frame1 = cursorResultFrame frame "marketParams" _ ptr1 from rfl,
      cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact hid
  have hcur1 : frame1.locals.get? cursorName = some (uint256Value ptr1) :=
    cursorResultFrame_cursor _ _ _ _
  have hloads1 := marketParamsLoads_of_fields hc1 hfields
  rcases supplyMorphoAccrualSimulation (frame := frame1) v (marketParamsData params)
      (by simp only [List.append, List.length_cons]; omega) rfl hm1 hp1 hfree1 hhi1
      hsrc hspan (by omega) hloads1 hs1 h1 with
    ⟨hbad, hrev⟩ | ⟨evm2, out2, aw2, k2, C2, hs2, hsource2, h2⟩
  · refine .inl ⟨fun tail ↦ ?_, hrev⟩
    apply cursorCallPrefix (by decide) hcall1
    exact hbad _
  let frame2 := supplyAccruedFrame frame1
  let mem2 := morphoAccrueReturnMem mem1 ptr1 (marketParamsData params)
  have hm2 : frame2.locals.get? "morphoTarget" = some (.address v.MORPHO) := by
    simpa only [frame2, supplyAccruedFrame,
      store_get_ne _ _ (by decide : ("__c1" == "morphoTarget") = false)] using hm1
  have hid2 : frame2.locals.get? "id" = some (wordBytes32Value id) := by
    simpa only [frame2, supplyAccruedFrame,
      store_get_ne _ _ (by decide : ("__c1" == "id") = false)] using hid1
  have hcur2 : frame2.locals.get? cursorName = some (uint256Value ptr1) := by
    simpa only [frame2, supplyAccruedFrame,
      store_get_ne _ _ (by decide : ("__c1" == cursorName) = false)] using hcur1
  have hprefix2 : MemoryPrefix mem1 mem2 ptr1.toNat := morphoAccrueReturnMem_prefix _ _ _
  rcases supplyMarketSimulation v (by simp only [List.append, List.length_cons]; omega)
      (morphoAccrueReturnMem_free _ _ _) hlo1 hhi1 hs2 h2 with
    ⟨evm3, ok, market, hcall, hh, hbad, hrev⟩ |
      ⟨evm3, market, aw3, k3, C3, hcall, hs3, hc3, hh3, hfit3,
        hfree3, hmem3, hfields3, hprefix3, h3⟩
  · rw [ha] at hcall
    refine .inl ⟨fun tail ↦ ?_, hrev⟩
    apply cursorCallPrefix (by decide) hcall1
    apply hsource2
    exact supplyMarketSourceReverts rfl hm2 hid2 hcur2 hcall hh hbad _
  rw [ha] at hcall
  let frame3 := supplyMorphoMarketFrame frame params ptr1 market
  let mem3 := marketReadMemory mem2 ptr1 id market
  let ptr3 := nextCursor ptr1 ⟨384⟩
  have hbound3 : ptr1.toNat + 384 < 2 ^ 64 :=
    (allocationFits_aligned _ ⟨384⟩ (by decide +kernel)).mp hfit3
  have hptr3 : ptr3.toNat = ptr1.toNat + 384 :=
    uadd_word_ofNat_toNat _ 384 (lt_trans hbound3 (by decide))
  have hmid : (nextCursor ptr1 ⟨192⟩).toNat = ptr1.toNat + 192 :=
    uadd_word_ofNat_toNat _ 192 (by change _ < 2 ^ 256; omega)
  have hid3 : frame3.locals.get? "id" = some (wordBytes32Value id) := by
    change (supplyMarketReservedFrame frame2 ptr1 market).locals.get? "id" = _
    simp only [supplyMarketReservedFrame, supplyMarketFrame,
      store_get_ne _ _ (by decide : (cursorName == "id") = false),
      store_get_ne _ _ (by decide : ("market" == "id") = false), hid2]
  have hcur3 : frame3.locals.get? cursorName = some (uint256Value ptr3) :=
    store_get_self _ _ _
  have hargs4 : evalExprs? config frame3 evm3
      [.immutable "MORPHO", .var "id", .env .this, .var cursorName] =
      .ok [.address v.MORPHO, wordBytes32Value id, .address I.codeOwner, uint256Value ptr3] := by
    have hm3 : evalExpr? config frame3 evm3 (.immutable "MORPHO") = .ok (.address v.MORPHO) :=
      evalImmutable_MORPHO _ _ _ _ _
    have he3 : evalExpr? config frame3 evm3 (.env .this) = .ok (.address I.codeOwner) := by
      simp only [evalExpr?, envValue, hs3.env, pure]
    simp only [evalExprs?, hm3, he3, evalExpr?, hid3, hcur3, EvalResult.ofOption,
      bind, EvalResult.bind, pure]
  obtain ⟨aw4, k4, C4, h4⟩ := metaMorphoV1_1_block_18106_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
  rcases supplySharesAllocationSimulation v (immStore v)
      (by simp only [List.append, List.length_cons]; omega) hcalldata hfree3
      (by rw [hptr3]; omega) (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) hs3 h4 with
    ⟨hbad, hrev⟩ | ⟨evm4, final4, shares, cursor, mem4, aw5, out4, k5, C5,
      hsource4, hs4, _, hfree4, hlo4, hhi4, hmem4, hprefix4, hmono4, h5⟩
  · simp only [Fin.toNat, haddr] at hbad
    refine .inl ⟨fun tail ↦ ?_, hrev⟩
    apply cursorCallPrefix (by decide) hcall1
    apply hsource2
    apply supplyMarketSourcePrefix rfl hm2 hid2 hcur2 hcall hc3 hh3 hfit3
    exact ExecBlock.consRevert (supplySharesReaderRevert hargs4 hbad)
  simp only [Fin.toNat, haddr] at hsource4
  have hcall4 := supplySharesReaderCall (ret := slotsAndCursorName) hargs4 hsource4
  have hprefixRest : MemoryPrefix mem1 mem4 ptr1.toNat :=
    hprefix2.trans (hprefix3.trans (hprefix4.mono (by rw [hptr3]; omega)))
  have hloads4 := hloads1.prefix hprefixRest hsrc (by omega) hspan
    (by change _ < 2 ^ 256; omega)
  have hfields4 (j : Nat) (hj : j < 2) :
      memLoad (nextCursor ptr1 ⟨192⟩ + UInt256.ofNat (32 * j)) mem4 =
        calldataWord market (32 * j) := by
    have hr := wordWindowPrefix_load (src := nextCursor ptr1 ⟨192⟩) (len := 64) hprefix4
      (by rw [hmid]; omega) (by rw [hmid]; rw [hptr3] at hmem3; omega)
      (by rw [hmid, hptr3]; omega) (by rw [hmid]; change _ < 2 ^ 256; omega)
    rw [hr (32 * j) (by omega)]
    exact hfields3 j (by omega)
  refine .inr ⟨evm4, params, market, mem4, out4, src, ptr1, shares, cursor,
    hs4, hc3, ?_, hfree4, hlo4, hhi4, hmem4, ?_,
    hprefix1.trans (hprefixRest.mono hmono1), hsrc, ?_, hloads4, ?_,
    hfields4 1 (by decide), aw5, k5, C5, h5⟩
  · intro tail result htail
    apply cursorCallPrefix (by decide) hcall1
    apply hsource2
    apply supplyMarketSourcePrefix rfl hm2 hid2 hcur2 hcall hc3 hh3 hfit3
    exact cursorCallPrefix (by decide) hcall4 htail
  · rw [hptr3] at hmono4
    omega
  · rw [hptr3] at hmono4
    omega
  · simpa only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
      u256_add_zero] using hfields4 0 (by decide)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
