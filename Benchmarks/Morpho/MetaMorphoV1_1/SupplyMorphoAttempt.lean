import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoLoopState
import Benchmarks.Morpho.MetaMorphoV1_1.MorphoSupplySimulation

/-! One optional supply call, with the caller's loop locals preserved across both outcomes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem supplyMorphoAttemptSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {frame : Frame} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params amount i assets : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 20 ≤ 1024)
    (hl : SupplyLoopLocals v frame i assets ptr)
    (hp : frame.locals.get? "marketParams" = some p.value)
    (ht : frame.locals.get? "toSupply" = some (uint256Value amount))
    (hs : SourceState s0 I σ evm)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hptr : ptr.toNat < 2 ^ 64)
    (hparamslo : 96 ≤ params.toNat) (hparams : params.toNat + 160 ≤ ptr.toNat)
    (hmem : params.toNat + 160 ≤ mem.size) (hloads : MarketParamsLoads mem params p)
    (hsub : amount.toNat ≤ assets.toNat)
    (rd : RD (deployedRuntime v) I g s0 (if amount = ⟨0⟩ then ⟨18168⟩ else ⟨18186⟩)
      ([params, amount, i, UInt256.ofNat v.MORPHO.toNat, assets] ++ R) mem aw rdata σ k C) :
    (ExecStmt config frame evm supplyMorphoSupply[0]! .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (frame' : Frame) (assets' cursor : UInt256) (mem' out : ByteArray),
      SourceState s0 I evm'.accountMap evm' ∧ SupplyLoopLocals v frame' i assets' cursor ∧
      memLoad ⟨64⟩ mem' = cursor ∧ cursor.toNat < 2 ^ 64 ∧ ptr.toNat ≤ cursor.toNat ∧
      MemoryPrefix mem mem' ptr.toNat ∧
      ExecStmt config frame evm supplyMorphoSupply[0]! (.ok frame' evm') ∧
      ∃ scratch0 scratch1 aw' k' C', RD (deployedRuntime v) I g s0 ⟨18168⟩
        ([scratch0, scratch1, i, UInt256.ofNat v.MORPHO.toNat, assets'] ++ R)
        mem' aw' out evm'.accountMap k' C' := by
  have htst := evalExpr_uint256_var_positive (cfg := config) evm "toSupply" amount ht
  by_cases hz : amount = ⟨0⟩
  · rw [if_pos hz] at rd
    have he : evalExpr? config frame evm (.binary .gt (.var "toSupply") (.intLit 0)) =
        .ok (.bool false) := by simpa only [hz, Nat.lt_irrefl, decide_false] using htst
    rw [hs.accounts] at rd
    exact .inr ⟨evm, frame, assets, ptr, mem, rdata, ⟨hs.world, hs.env, rfl⟩, hl,
      hfree, hptr, le_refl _, .refl _ _, ExecStmt.iteFalse he ExecBlock.nil, params, amount, aw, k, C, rd⟩
  · rw [if_neg hz] at rd
    have hpos : 0 < amount.toNat :=
      Nat.pos_of_ne_zero (fun h ↦ hz (uint256_toNat_eq_zero h))
    rw [decide_eq_true hpos] at htst
    have ha : AccountAddress.ofUInt256 (UInt256.ofNat v.MORPHO.toNat) = v.MORPHO := by
      rw [accountAddress_ofUInt256_eq_ofNat_toNat]
      exact accountAddress_of_word_val _
    have hlocals : SupplyCallLocals frame v.MORPHO p ptr assets amount :=
      ⟨hl.contract, hl.target, hp, hl.cursor, hl.assets, ht⟩
    rcases morphoSupplySimulation v p hstack hs hfree hptr hparamslo hparams hmem hloads hsub rd with
      ⟨evm', out, hcall, hh, hbad, hrev⟩ |
        ⟨evm', ok, out, mem', cursor, aw', k', C', hcall, hs', hh, hgood,
          hcursor, hfree', hptr', hmono, hprefix, hdone⟩
    · rw [ha, ← hs.env] at hcall
      exact .inl ⟨ExecStmt.iteTrue htst
        (ExecBlock.consRevert (supplyCallSourceReverts hlocals hcall hh hbad)), hrev⟩
    · rw [ha, ← hs.env] at hcall
      cases ok with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte] at hcursor hdone
          rw [hcursor] at hfree' hptr' hmono
          exact .inr ⟨evm', supplyCallFailureFrame frame out, assets, ptr, mem', out, hs',
            hl.callFailure out, hfree', hptr', hmono, hprefix,
            ExecStmt.iteTrue htst (ExecBlock.consNormal
              (supplyCallSourceFailure hlocals hcall) ExecBlock.nil), amount, amount, aw', k', C', hdone⟩
      | true =>
          simp only [↓reduceIte] at hcursor hdone
          rw [hcursor] at hfree' hptr' hmono
          exact .inr ⟨evm', supplyCallSuccessFrame frame ptr assets amount out,
            UInt256.sub assets amount, nextCursor ptr ⟨64⟩, mem', out, hs',
            hl.callSuccess amount out, hfree', hptr', hmono, hprefix,
            ExecStmt.iteTrue htst (ExecBlock.consNormal
              (supplyCallSourceSuccess hlocals hcall hh (hgood rfl).1 (hgood rfl).2 hsub) ExecBlock.nil),
            ⟨0⟩, ⟨0⟩, aw', k', C', hdone⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
