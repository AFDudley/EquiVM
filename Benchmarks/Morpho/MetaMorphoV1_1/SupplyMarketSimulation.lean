import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMarketCall
import Benchmarks.Morpho.MetaMorphoV1_1.MarketReadDecode

/-! The supply loop's complete market read, with arbitrary callee state and return bytes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem supplyMarketSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr id cap params i morpho : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 18 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hptr : ptr.toNat < 2 ^ 64)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨18057⟩
      (⟨0⟩ :: id :: cap :: params :: i :: morpho :: R) mem aw rdata σ k C) :
    (∃ evm' ok out, typedCallViaEVM config evm (AccountAddress.ofUInt256 morpho)
      "market" 0 [wordBytes32Value id] (ok, evm', out) false ∧ out.size < 2 ^ 255 ∧
      (ok = false ∨ ¬ (MarketChecks out ∧ allocationFits ptr ⟨384⟩)) ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      typedCallViaEVM config evm (AccountAddress.ofUInt256 morpho) "market" 0
        [wordBytes32Value id] (true, evm', out) false ∧
      SourceState s0 I evm'.accountMap evm' ∧ MarketChecks out ∧ out.size < 2 ^ 255 ∧
      allocationFits ptr ⟨384⟩ ∧
      memLoad ⟨64⟩ (marketReadMemory mem ptr id out) = nextCursor ptr ⟨384⟩ ∧
      (nextCursor ptr ⟨384⟩).toNat ≤ (marketReadMemory mem ptr id out).size ∧
      (∀ j, j < 6 → memLoad (nextCursor ptr ⟨192⟩ + UInt256.ofNat (32 * j))
        (marketReadMemory mem ptr id out) = calldataWord out (32 * j)) ∧
      MemoryPrefix mem (marketReadMemory mem ptr id out) ptr.toNat ∧
      RD (deployedRuntime v) I g s0 ⟨18106⟩
        (⟨18119⟩ :: id :: nextCursor ptr ⟨192⟩ :: ⟨18144⟩ :: cap :: params :: i :: morpho :: R)
        (marketReadMemory mem ptr id out) aw' out evm'.accountMap k' C' := by
  obtain ⟨gasArg, aw1, k1, C1, h1⟩ := supplyMarketReachStaticcall v (by omega) hfree hptr rd
  obtain ⟨evm', ok, out, aw2, k2, C2, hcall, hs', hout, h2⟩ :=
    supplyMarketStaticcall v (by simp only [List.length_cons]; omega) hs h1
  have hhi : out.size < 2 ^ 255 := lt_trans (marketReturnSize hcall) (by decide)
  cases ok with
  | false =>
      exact .inl ⟨evm', false, out, hcall, hhi, .inl rfl,
        supplyMarketCallFailure v (by simp only [List.length_cons]; omega) hout h2⟩
  | true =>
      rcases supplyMarketReturnAllocation v (by simp only [List.length_cons]; omega) hout h2 with
        ⟨hbad, hrev⟩ | ⟨hlong, hfit, aw3, k3, C3, h3⟩
      · exact .inl ⟨evm', true, out, hcall, hhi, .inr (fun hc ↦ hbad ⟨hc.1.1, hc.2⟩), hrev⟩
      · rcases marketReadDecode v (by simp only [List.length_cons]; omega) hlo hlong hout hfit
            (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h3 with
          ⟨hbad, hrev⟩ | ⟨hc, aw4, k4, C4, hfree', hsize', hfields, hprefix, h4⟩
        · exact .inl ⟨evm', true, out, hcall, hhi, .inr (fun hc ↦ hbad hc.1), hrev⟩
        · obtain ⟨aw5, k5, C5, h5⟩ := metaMorphoV1_1_block_18320_packed
            (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
            (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h4
          exact .inr ⟨evm', out, aw5, k5, C5, hcall, hs', hc, hhi, hfit,
            hfree', hsize', hfields, hprefix, h5⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
