import Benchmarks.Morpho.MetaMorphoV1_1.MarketReadDecode
import Benchmarks.Morpho.MetaMorphoV1_1.MarketBalancesAllocationSource

/-! Source/bytecode correspondence through the market reader and its decoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem marketReadSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params morpho : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 12 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hptr : ptr.toNat < 2 ^ 64)
    (hparams : mem.readWithPadding params.toNat 160 = p.bytes)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨16911⟩ (morpho :: params :: R)
      mem aw rdata σ k C) :
    (ExecFuncBody config
        (allocatedMarketBalancesFrame (immStore v) (AccountAddress.ofNat morpho.toNat) p ptr)
        evm allocatedMarketBalancesFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      typedCallViaEVM config evm (AccountAddress.ofNat morpho.toNat) "market" 0
        [wordBytes32Value p.id] (true, evm', out) false ∧
      SourceState s0 I evm'.accountMap evm' ∧ MarketChecks out ∧ out.size < 2 ^ 255 ∧
      allocationFits ptr ⟨384⟩ ∧
      memLoad ⟨64⟩ (marketReadMemory mem ptr p.id out) = nextCursor ptr ⟨384⟩ ∧
      (nextCursor ptr ⟨384⟩).toNat ≤ (marketReadMemory mem ptr p.id out).size ∧
      (∀ i, i < 6 → memLoad (nextCursor ptr ⟨192⟩ + UInt256.ofNat (32 * i))
        (marketReadMemory mem ptr p.id out) = calldataWord out (32 * i)) ∧
      MemoryPrefix mem (marketReadMemory mem ptr p.id out) ptr.toNat ∧
      RD (deployedRuntime v) I g s0 ⟨16966⟩ (⟨0⟩ :: params :: nextCursor ptr ⟨192⟩ :: R)
        (marketReadMemory mem ptr p.id out) aw' out evm'.accountMap k' C' := by
  obtain ⟨gasArg, aw1, k1, C1, h1⟩ := marketReachStaticcall v p (by omega)
    hfree hptr hparams rd
  obtain ⟨evm', ok, out, aw2, k2, C2, hcall, hs', hout, h2⟩ :=
    marketStaticcall v (by omega) hs h1
  have hhi : out.size < 2 ^ 255 := lt_trans (marketReturnSize hcall) (by decide)
  cases ok with
  | false =>
      exact .inl ⟨allocatedMarketBalancesBodyCallReverts hcall,
        marketCallFailure v (by omega) hout h2⟩
  | true =>
      rcases marketReturnAllocation v hstack hout h2 with
        ⟨hbad, hrev⟩ | ⟨hlong, hfit, aw3, k3, C3, h3⟩
      · refine .inl ⟨?_, hrev⟩
        by_cases hc : MarketChecks out
        · exact allocatedMarketBalancesBodyAllocationReverts hcall
            (by rw [marketDecode hhi, if_pos hc]) (fun hf ↦ hbad ⟨hc.1, hf⟩)
        · exact allocatedMarketBalancesBodyDecodeReverts hcall
            (by rw [marketDecode hhi, if_neg hc])
      · rcases marketReadDecode v (by simp only [List.length_cons]; omega) hlo hlong hout
            hfit (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h3 with
          ⟨hbad, hrev⟩ | ⟨hc, aw4, k4, C4, hfree', hsize', hfields, hprefix, h4⟩
        · exact .inl ⟨allocatedMarketBalancesBodyDecodeReverts hcall
            (by rw [marketDecode hhi, if_neg hbad]), hrev⟩
        · obtain ⟨aw5, k5, C5, h5⟩ := metaMorphoV1_1_block_17648_packed
            (immWords := wordsOf (immStore v)) (by omega)
            (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h4
          exact .inr ⟨evm', out, aw5, k5, C5, hcall, hs', hc, hhi, hfit,
            hfree', hsize', hfields, hprefix, h5⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
