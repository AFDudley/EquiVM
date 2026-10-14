import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateAccruedSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateWithdrawBranch
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateSupplyBranch

/-! Accrual and the two reallocation branches for one enabled, decoded row. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false
attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem reallocateRowContinuationSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {values : List Value} {mem row : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {ptr allocation params withdrawn id offset i len supplied saved : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 29 ≤ 1024)
    (hl : ReallocateLocals v frame values i supplied withdrawn ptr)
    (hrow : frame.locals.get? "allocation" = some (reallocateAllocationValue row))
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hcalldata : I.calldata.size < UInt256.size)
    (halloc : memLoad allocation mem = params)
    (hasset : memLoad (allocation + ⟨32⟩) mem = calldataWord row 160)
    (halloclo : 96 ≤ allocation.toNat) (hallocspan : allocation.toNat + 64 ≤ ptr.toNat)
    (hallocmem : allocation.toNat + 64 ≤ mem.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hptr : ptr.toNat < 2 ^ 64)
    (hparamslo : 96 ≤ params.toNat) (hspan : params.toNat + 160 ≤ ptr.toNat)
    (hmem : params.toNat + 160 ≤ mem.size) (hloads : MarketParamsLoads mem params (marketParamsData row))
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨6152⟩
      ([allocation + ⟨32⟩, allocation, withdrawn, id, offset, i, len, supplied, saved] ++ R)
      mem aw rdata σ k C) :
    (ExecBlock config frame evm reallocateRowContinuation .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    (ExecBlock config frame evm reallocateRowContinuation .staticViolation ∧ RDstatic (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (mem' out : ByteArray)
      (aw' supplied' withdrawn' ptr' : UInt256) (k' C' : Nat),
      SourceState s0 I evm'.accountMap evm' ∧ ReallocateLocals v frame' values i supplied' withdrawn' ptr' ∧
      (ExecBlock config frame evm reallocateRowContinuation (.ok frame' evm') ∨
        ExecBlock config frame evm reallocateRowContinuation (.continue frame' evm')) ∧
      memLoad ⟨64⟩ mem' = ptr' ∧ 96 ≤ ptr'.toNat ∧ ptr'.toNat < 2 ^ 64 ∧
      MemoryPrefix mem mem' ptr.toNat ∧
      RD (deployedRuntime v) I g s0 ⟨6380⟩
        ([i, ⟨1⟩, offset, withdrawn', len, supplied', saved] ++ R)
        mem' aw' out evm'.accountMap k' C' := by
  rcases reallocateAccruedSimulation v (by dsimp only [List.append, List.length_cons]; omega)
      hl hrow hid hcalldata hfree hlo halloc hparamslo hspan hmem hloads hs rd with
    ⟨hbad, hrev⟩ | ⟨evm1, frame1, market, shares, result, out1, aw1, k1, C1,
      hs1, hl1, hr1, hi1, ha1, hsh1, hacc, h1⟩
  · exact .inl ⟨execBlockAppendReverted hbad, hrev⟩
  have hal1 : memLoad allocation result.memory = params := by
    have hh := result.preserves.load_preserved halloclo (by omega) (by omega) allocation.val.isLt
    rw [u256_ofNat_toNat] at hh
    exact hh.trans halloc
  have hap : (allocation + ⟨32⟩).toNat = allocation.toNat + 32 :=
    uadd_word_ofNat_toNat allocation 32 (by change _ < 2 ^ 256; omega)
  have has1 : memLoad (allocation + ⟨32⟩) result.memory = calldataWord row 160 := by
    have hh := result.preserves.load_preserved (off := (allocation + ⟨32⟩).toNat)
      (by omega) (by omega) (by omega) (by change _ < 2 ^ 256; omega)
    rw [u256_ofNat_toNat] at hh
    exact hh.trans hasset
  have hloads1 := hloads.prefix result.preserves hparamslo hmem hspan (by change _ < 2 ^ 256; omega)
  let assets := assetsDownWord shares (calldataWord market 0) (calldataWord market 32)
  let amount := UInt256.ofNat (assets.toNat - (calldataWord row 160).toNat)
  let frame2 := reallocateAmountFrame frame1 assets (calldataWord row 160)
  have hl2 : ReallocateLocals v frame2 values i supplied withdrawn result.cursor :=
    hl1.amount assets (calldataWord row 160)
  have hr2 : frame2.locals.get? "allocation" = some (reallocateAllocationValue row) := by
    dsimp only [frame2, reallocateAmountFrame]
    rw [store_get_ne _ _ (by decide)]; exact hr1
  have hi2 : frame2.locals.get? "id" = some (wordBytes32Value id) := by
    dsimp only [frame2, reallocateAmountFrame]
    rw [store_get_ne _ _ (by decide)]; exact hi1
  have ha2 : frame2.locals.get? "supplyAssets" = some (uint256Value assets) := by
    dsimp only [frame2, reallocateAmountFrame]
    rw [store_get_ne _ _ (by decide)]; exact ha1
  have hsh2 : frame2.locals.get? "supplyShares" = some (uint256Value shares) := by
    dsimp only [frame2, reallocateAmountFrame]
    rw [store_get_ne _ _ (by decide)]; exact hsh1
  have hm2 : frame2.locals.get? "withdrawn" = some (uint256Value amount) := store_get_self _ _ _
  have hamount := reallocateAmountSource (evm := evm1) hl1.contract ha1 hr1
  have wrap {outcome : ExecResult} (hbranch : ExecStmt config frame2 evm1 reallocateRowBranch outcome) :
      ExecBlock config frame evm reallocateRowContinuation outcome :=
    execBlockAppendOk hacc (ExecBlock.consNormal hamount (execBlock_singleton hbranch))
  have htest := evalExpr_uint256_var_positive (cfg := config) evm1 "withdrawn" amount hm2
  obtain ⟨aw2, k2, C2, h2⟩ := reallocateAmountRuntime v
    (by dsimp only [List.append, List.length_cons]; omega) has1 h1
  by_cases hz : amount = ⟨0⟩
  · have ht : ¬ 0 < amount.toNat := by rw [hz]; decide
    rw [decide_eq_false ht] at htest
    rw [if_pos hz] at h2
    rcases reallocateSupplyBranch v (by omega) hl2 hr2 hi2 ha2 hal1 halloclo
        (le_trans (by omega) result.cursorLower) (le_trans (by omega) result.preserves.size)
        result.free result.lower result.upper hparamslo (le_trans hspan result.cursorLower)
        (le_trans hmem result.preserves.size) hloads1 hs1 h2 with
      ⟨hbad, hrev⟩ | ⟨hstatic, hsrev⟩ |
        ⟨evm3, frame3, mem3, out3, aw3, supplied3, ptr3, k3, C3, hs3, hl3, hsource,
          hf3, hlo3, hhi3, hp3, h3⟩
    · exact .inl ⟨wrap (ExecStmt.iteFalse htest hbad), hrev⟩
    · exact .inr (.inl ⟨wrap (ExecStmt.iteFalse htest hstatic), hsrev⟩)
    · refine .inr (.inr ⟨evm3, frame3, mem3, out3, aw3, supplied3, withdrawn, ptr3, k3, C3,
        hs3, hl3, ?_, hf3, hlo3, hhi3, result.preserves.trans (hp3.mono result.cursorLower), h3⟩)
      exact hsource.elim (fun h ↦ .inl (wrap (ExecStmt.iteFalse htest h)))
        (fun h ↦ .inr (wrap (ExecStmt.iteFalse htest h)))
  · have ht : 0 < amount.toNat := by
      have hn : amount.toNat ≠ 0 := fun h ↦ hz (uint256_toNat_eq_zero h)
      omega
    rw [decide_eq_true ht] at htest
    rw [if_neg hz] at h2
    rcases reallocateWithdrawBranch v (by omega) hl2 hr2 hi2 hsh2 hm2 hal1 has1
        result.free result.lower result.upper hparamslo (le_trans hspan result.cursorLower)
        (le_trans hmem result.preserves.size) hloads1 hs1 h2 with
      ⟨hbad, hrev⟩ | ⟨hstatic, hsrev⟩ |
        ⟨evm3, frame3, mem3, out3, aw3, k3, C3, hs3, hl3, hsource, hf3, hlo3, hhi3, hp3, h3⟩
    · exact .inl ⟨wrap (ExecStmt.iteTrue htest hbad), hrev⟩
    · exact .inr (.inl ⟨wrap (ExecStmt.iteTrue htest hstatic), hsrev⟩)
    · exact .inr (.inr ⟨evm3, frame3, mem3, out3, aw3, supplied, withdrawn + calldataWord out3 0,
        nextCursor result.cursor ⟨64⟩, k3, C3, hs3, hl3, .inl (wrap (ExecStmt.iteTrue htest hsource)),
        hf3, hlo3, hhi3, result.preserves.trans (hp3.mono result.cursorLower), h3⟩)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
