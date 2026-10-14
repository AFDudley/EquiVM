import Benchmarks.Morpho.MetaMorphoV1_1.AccruedSupplyPrefixSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.AccruedSupplyTailSource
import Benchmarks.Morpho.MetaMorphoV1_1.SupplySharesAllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.SharesToAssetsDownRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_062

/-! Complete accrued-supply-balance simulation, retaining the market representation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem accruedSupplySimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params id ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 20 ≤ 1024)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hparamslo : 96 ≤ params.toNat) (hspan : params.toNat + 160 ≤ ptr.toNat)
    (hmem : params.toNat + 160 ≤ mem.size) (hloads : MarketParamsLoads mem params p)
    (hs : SourceState s0 I σ evm)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨14951⟩ (params :: id :: ret :: R) mem aw rdata σ k C) :
    (ExecFuncBody config (accruedSupplyFrame (immStore v) p id ptr) evm
      allocatedAccruedSupplyBalanceFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (final : Frame) (market : ByteArray) (shares : UInt256)
      (result : AccruedSupplyMarketResult mem ptr market) (out : ByteArray)
      (aw' : UInt256) (k' C' : Nat),
      SourceState s0 I evm'.accountMap evm' ∧ MarketChecks market ∧
      ExecFuncBody config (accruedSupplyFrame (immStore v) p id ptr) evm
        allocatedAccruedSupplyBalanceFunction.body
        (.returned final evm' (some [accruedSupplyValue market shares, uint256Value result.cursor])) ∧
      RD (deployedRuntime v) I g s0 ret
        (result.marketPtr :: shares :: assetsDownWord shares (calldataWord market 0)
          (calldataWord market 32) :: R) result.memory aw' out evm'.accountMap k' C' := by
  rcases accruedSupplyPrefixSimulation v p (by simp only [List.length_cons]; omega)
      hfree hlo hparamslo hspan hmem hloads hs rd with
    hbad | ⟨evm1, frame1, market, result1, aw1, k1, C1, hs1, hc, hl1, hpre, h1⟩
  · exact .inl hbad
  rcases frame1 with ⟨cc, locals, imms⟩
  have hcc := hl1.contract
  have himms := hl1.imms
  dsimp only at hcc himms
  subst cc
  subst imms
  let frame1 : Frame := { contract := contract, locals := locals, immutables := immStore v }
  have hid : frame1.locals.get? "id" = some (wordBytes32Value id) := hl1.id
  have hcursor : frame1.locals.get? cursorName = some (uint256Value result1.cursor) := hl1.cursor
  have hargs : evalExprs? config frame1 evm1
      [.immutable "MORPHO", .var "id", .env .this, .var cursorName] =
      .ok [.address v.MORPHO, wordBytes32Value id, .address I.codeOwner, uint256Value result1.cursor] := by
    have hm : evalExpr? config frame1 evm1 (.immutable "MORPHO") = .ok (.address v.MORPHO) :=
      evalImmutable_MORPHO _ _ _ _ _
    have he : evalExpr? config frame1 evm1 (.env .this) = .ok (.address I.codeOwner) := by
      simp only [evalExpr?, envValue, hs1.env, pure]
    simp only [evalExprs?, hm, he, evalExpr?, hid, hcursor,
      EvalResult.ofOption, bind, EvalResult.bind, pure]
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_15141_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  have ha (a : AccountAddress) : AccountAddress.ofNat (UInt256.ofNat a.val).toNat = a := by
    rw [UInt256.toNat_ofNat_of_lt (lt_of_lt_of_le a.isLt (by decide))]
    exact accountAddress_ofNat_toNat a
  rcases supplySharesAllocationSimulation v (immStore v)
      (by simp only [List.length_cons]; omega) hcalldata result1.free result1.lower
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) hs1 h2 with
    ⟨hbad, hrev⟩ | ⟨evm2, final2, shares, ptr2, mem2, aw3, out2, k3, C3,
      hsource2, hs2, _, hfree2, hlo2, hhi2, hmem2, hprefix2, hmono2, h3⟩
  · simp only [Fin.toNat, ha] at hbad
    exact .inl ⟨ExecFuncBody.execBlockRevert (hpre _
      (ExecBlock.consRevert (supplySharesReaderRevert hargs hbad))), hrev⟩
  simp only [Fin.toNat, ha] at hsource2
  have hcall2 := supplySharesReaderCall (ret := slotsAndCursorName) hargs hsource2
  let frame2 := cursorResultFrame frame1 "__c2" (uint256Value shares) ptr2
  have hsval : frame2.locals.get? "__c2" = some (uint256Value shares) :=
    cursorResultFrame_value _ _ _ _ (by decide)
  have hsold : frame2.locals.get? "shares" = some (.int 0) := by
    rw [cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact hl1.shares
  have haold : frame2.locals.get? "assets" = some (.int 0) := by
    rw [cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact hl1.assets
  have hmval : frame2.locals.get? "market" = some (marketValue market) := by
    rw [cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact hl1.market
  have hptrval : frame2.locals.get? cursorName = some (uint256Value ptr2) :=
    cursorResultFrame_cursor _ _ _ _
  have hfields2 (i : Nat) (hi : i < 6) :
      memLoad (result1.marketPtr + UInt256.ofNat (32 * i)) mem2 = calldataWord market (32 * i) := by
    rw [wordWindowPrefix_load hprefix2 result1.marketLower
      (by have h := result1.marketSpan; have hm := result1.size; omega)
      result1.marketSpan
      (by have h := result1.marketSpan; have hh := result1.upper; change _ < 2 ^ 256; omega)
      (32 * i) (by omega)]
    exact result1.fields i hi
  have hf0 : memLoad result1.marketPtr mem2 = calldataWord market 0 := by
    simpa only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
      u256_add_zero] using hfields2 0 (by decide)
  have hf32 : memLoad (result1.marketPtr + UInt256.ofNat 32) mem2 = calldataWord market 32 :=
    hfields2 1 (by decide)
  have hc0 : UInt256.land (calldataWord market 0) uint128Mask = calldataWord market 0 :=
    u256LandMaskCleanOfToNat _ _ (by decide +kernel) hc.2.1
  have hc32 : UInt256.land (calldataWord market 32) uint128Mask = calldataWord market 32 :=
    u256LandMaskCleanOfToNat _ _ (by decide +kernel) hc.2.2.1
  unfold uint128Mask at hc0 hc32
  obtain ⟨aw4, k4, C4, h4⟩ := metaMorphoV1_1_block_15158_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
  simp only [metaMorphoV1_1_block_15158_stack, hf0, hf32, hc0, hc32] at h4
  by_cases hfit : assetsDownFits shares (calldataWord market 0) (calldataWord market 32)
  · obtain ⟨k5, C5, h5⟩ := assetsDownReturn v
      (by simp only [List.length_cons]; omega) hfit
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h4
    obtain ⟨aw6, k6, C6, h6⟩ := metaMorphoV1_1_block_12410_packed
      (immWords := wordsOf (immStore v)) (by omega) hret h5
    let result : AccruedSupplyMarketResult mem ptr market :=
      { memory := mem2
        cursor := ptr2
        marketPtr := result1.marketPtr
        free := hfree2
        cursorLower := le_trans result1.cursorLower hmono2
        lower := hlo2
        upper := hhi2
        size := hmem2
        marketLower := result1.marketLower
        marketSpan := le_trans result1.marketSpan hmono2
        fields := hfields2
        preserves := result1.preserves.trans (hprefix2.mono result1.cursorLower) }
    refine .inr ⟨evm2, accruedSupplyFinalFrame frame2 market shares, market, shares, result,
      out2, aw6, k6, C6, hs2, hc, ExecFuncBody.execBlockRet (hpre _ ?_), h6⟩
    apply cursorCallPrefix (by decide) hcall2
    exact accruedSupplyTailReturns (frame := frame2) rfl hsval hsold haold hmval hptrval hfit
  · refine .inl ⟨ExecFuncBody.execBlockRevert (hpre _ ?_),
      assetsDownRevert v (by simp only [List.length_cons]; omega) hfit h4⟩
    apply cursorCallPrefix (by decide) hcall2
    exact accruedSupplyTailReverts (frame := frame2) rfl hsval hsold hmval hfit

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
