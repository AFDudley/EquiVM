import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawMorphoReadersSource
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsAllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsDecoded
import Benchmarks.Morpho.MetaMorphoV1_1.AccruedSupplySimulation
import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawableSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_084

/-! Compose market parameters, accrued balances, and available liquidity before a
withdrawal attempt. The accrual call carries its actual post-state through every reader. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem withdrawMorphoReadersSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr id i assets : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 27 ≤ 1024)
    (hl : WithdrawMorphoLocals v frame i assets ptr)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨16116⟩
      ([id, ⟨18704⟩, ⟨18711⟩, ⟨18738⟩, id, i, assets] ++ R) mem aw rdata σ k C) :
    ((∀ tail, ExecBlock config frame evm (withdrawMorphoReaders ++ tail) .reverted) ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (p : MarketParamsData) (mem' out : ByteArray)
      (params cursor liquidity : UInt256),
      SourceState s0 I evm'.accountMap evm' ∧ WithdrawMorphoLocals v frame' i assets cursor ∧
      frame'.locals.get? "marketParams" = some p.value ∧
      frame'.locals.get? "__c2" = some (uint256Value liquidity) ∧
      (∀ tail outcome, ExecBlock config frame' evm' tail outcome →
        ExecBlock config frame evm (withdrawMorphoReaders ++ tail) outcome) ∧
      memLoad ⟨64⟩ mem' = cursor ∧ 96 ≤ cursor.toNat ∧ cursor.toNat < 2 ^ 64 ∧
      cursor.toNat ≤ mem'.size ∧ ptr.toNat ≤ cursor.toNat ∧
      MemoryPrefix mem mem' ptr.toNat ∧
      96 ≤ params.toNat ∧ params.toNat + 160 ≤ cursor.toNat ∧
      MarketParamsLoads mem' params p ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨18738⟩
        ([liquidity, params, i, assets] ++ R) mem' aw' out evm'.accountMap k' C' := by
  rcases frame with ⟨c, locals, imms⟩
  have hcontract := hl.contract
  have himms := hl.imms
  dsimp only at hcontract himms
  subst c
  subst imms
  let frame : Frame := { contract := contract, locals := locals, immutables := immStore v }
  have hcursor : frame.locals.get? cursorName = some (uint256Value ptr) := hl.cursor
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
  let p := marketParamsData params
  let frame1 := cursorResultFrame frame "marketParams" p.value ptr1
  have hl1 : WithdrawMorphoLocals v frame1 i assets ptr1 :=
    hl.reader _ _ _ (by decide) (by decide) (by decide) (by decide)
  have hp1 : frame1.locals.get? "marketParams" = some p.value :=
    cursorResultFrame_value _ _ _ _ (by decide)
  have hid1 : frame1.locals.get? "id" = some (wordBytes32Value id) := by
    rw [cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact hid
  have hcur1 : frame1.locals.get? cursorName = some (uint256Value ptr1) := hl1.cursor
  have hargs2 : evalExprs? config frame1 evm1 [.var "marketParams", .var "id", .var cursorName] =
      .ok [p.value, wordBytes32Value id, uint256Value ptr1] := by
    simp only [evalExprs?, evalExpr?, hp1, hid1, hcur1,
      EvalResult.ofOption, bind, EvalResult.bind, pure]
  have hloads1 := marketParamsLoads_of_fields hc1 hfields
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_18704_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  rcases accruedSupplySimulation v p (by simp only [List.append, List.length_cons]; omega)
      hcalldata hfree1 hlo1 hsrc hspan (by omega) hloads1 hs1
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2 with
    ⟨hbad, hrev⟩ | ⟨evm2, final2, market, shares, result2, out2, aw3, k3, C3,
      hs2, hc2, hsource2, h3⟩
  · refine .inl ⟨fun tail ↦ ?_, hrev⟩
    apply cursorCallPrefix (by decide) hcall1
    exact ExecBlock.consRevert (accruedSupplyReaderRevert hargs2 hbad)
  have hcall2 := accruedSupplyReaderCall (ret := slotsAndCursorName) hargs2 hsource2
  let frame2 := cursorResultFrame frame1 "__c1" (accruedSupplyValue market shares) result2.cursor
  have hl2 : WithdrawMorphoLocals v frame2 i assets result2.cursor :=
    hl1.reader _ _ _ (by decide) (by decide) (by decide) (by decide)
  have hp2 : frame2.locals.get? "marketParams" = some p.value := by
    rw [cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact hp1
  have hb2 : frame2.locals.get? "__c1" = some (accruedSupplyValue market shares) :=
    cursorResultFrame_value _ _ _ _ (by decide)
  let frame3 := withdrawMorphoBalancesFrame frame2 market shares
  have hbalances := withdrawMorphoBalancesSource (evm := evm2) hb2
  have hl3 : WithdrawMorphoLocals v frame3 i assets result2.cursor := hl2.balances market shares
  have hp3 : frame3.locals.get? "marketParams" = some p.value := by
    rw [withdrawMorphoBalancesFrame_preserves _ _ _ _ (by decide) (by decide)]
    exact hp2
  have hm3 : frame3.locals.get? "market" = some (marketValue market) :=
    withdrawMorphoBalancesFrame_market _ _ _
  have ha3 : frame3.locals.get? "supplyAssets" = some (uint256Value
      (assetsDownWord shares (calldataWord market 0) (calldataWord market 32))) :=
    withdrawMorphoBalancesFrame_assets _ _ _
  have hcur3 : frame3.locals.get? cursorName = some (uint256Value result2.cursor) := hl3.cursor
  have hargs3 : evalExprs? config frame3 evm2
      [.var "marketParams", .field (.var "market") "totalSupplyAssets",
        .field (.var "market") "totalBorrowAssets", .var "supplyAssets", .var cursorName] =
      .ok [p.value, uint256Value (calldataWord market 0), uint256Value (calldataWord market 64),
        uint256Value (assetsDownWord shares (calldataWord market 0) (calldataWord market 32)),
        uint256Value result2.cursor] := by
    have he0 : evalExpr? config frame3 evm2 (.field (.var "market") "totalSupplyAssets") =
        .ok (uint256Value (calldataWord market 0)) := marketFieldSource hm3 rfl
    have he64 : evalExpr? config frame3 evm2 (.field (.var "market") "totalBorrowAssets") =
        .ok (uint256Value (calldataWord market 64)) := marketFieldSource hm3 rfl
    simp only [evalExprs?, he0, he64, evalExpr?, hp3, ha3, hcur3,
      EvalResult.ofOption, bind, EvalResult.bind, pure]
  have hloads2 : MarketParamsLoads result2.memory src p :=
    hloads1.prefix result2.preserves hsrc (by omega) hspan
      (by change _ < 2 ^ 256; omega)
  have hf0 : memLoad result2.marketPtr result2.memory = calldataWord market 0 := by
    simpa only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,
      u256_add_zero] using result2.fields 0 (by decide)
  have hf64 : memLoad (result2.marketPtr + UInt256.ofNat 64) result2.memory =
      calldataWord market 64 := result2.fields 2 (by decide)
  have hmask (w : UInt256) (hw : w.toNat < 2 ^ 128) :
      UInt256.land w (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
        (UInt256.ofNat 1)) = w :=
    u256LandMaskCleanOfToNat _ _ (by decide +kernel) hw
  obtain ⟨aw4, k4, C4, h4⟩ := metaMorphoV1_1_block_18711_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
  simp only [metaMorphoV1_1_block_18711_stack, hf0, hf64,
    hmask _ hc2.2.1, hmask _ hc2.2.2.2.1] at h4
  rcases withdrawableSimulation v p (by simp only [List.append, List.length_cons]; omega)
      result2.free result2.lower result2.upper hloads2.1 hs2
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h4 with
    ⟨hbad, hrev⟩ | ⟨evm4, final4, liquidity, cursor, mem4, out4,
      hs4, _, hsource4, hfree4, hlo4, hhi4, hmem4, hprefix4, hmono4, hdone⟩
  · refine .inl ⟨fun tail ↦ ?_, hrev⟩
    apply cursorCallPrefix (by decide) hcall1
    apply cursorCallPrefix (by decide) hcall2
    apply execBlock_append_ok hbalances
    exact ExecBlock.consRevert
      (internalCallFunctionRevert (callee := allocatedWithdrawableFunction) hargs3 rfl rfl hbad)
  have hcall4 := internalCallFunctionReturn (retVar := slotsAndCursorName)
    (name := allocatedWithdrawableFunction.name)
    (callee := allocatedWithdrawableFunction) hargs3 rfl rfl hsource4
  let frame4 := cursorResultFrame frame3 "__c2" (uint256Value liquidity) cursor
  have hl4 : WithdrawMorphoLocals v frame4 i assets cursor :=
    hl3.reader _ _ _ (by decide) (by decide) (by decide) (by decide)
  have hp4 : frame4.locals.get? "marketParams" = some p.value := by
    rw [cursorResultFrame_preserves _ _ _ _ _ (by decide) (by decide) (by decide)]
    exact hp3
  have hspan2 : src.toNat + 160 ≤ result2.cursor.toNat := le_trans hspan result2.cursorLower
  have hloads4 : MarketParamsLoads mem4 src p := hloads2.prefix hprefix4 hsrc
    (le_trans hspan2 result2.size) hspan2
    (by have hh := result2.upper; change _ < 2 ^ 256; omega)
  refine .inr ⟨evm4, frame4, p, mem4, out4, src, cursor, liquidity,
    hs4, hl4, hp4, cursorResultFrame_value _ _ _ _ (by decide), ?_,
    hfree4, hlo4, hhi4, hmem4, le_trans hmono1 (le_trans result2.cursorLower hmono4),
    hprefix1.trans (result2.preserves.trans (hprefix4.mono result2.cursorLower) |>.mono hmono1),
    hsrc, le_trans hspan2 hmono4, hloads4, hdone⟩
  intro tail outcome htail
  apply cursorCallPrefix (by decide) hcall1
  apply cursorCallPrefix (by decide) hcall2
  apply execBlock_append_ok hbalances
  exact cursorCallPrefix (by decide) hcall4 htail

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
