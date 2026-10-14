import Benchmarks.Morpho.MetaMorphoV1_1.MarketReadDecode

/-! The market STATICCALL, return allocation, and decoder used after interest accrual. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem accruedSupplyMarketAllocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr saved id : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 15 ≤ 1024)
    (hout : out.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨15129⟩ (⟨1⟩ :: ptr :: saved :: id :: ⟨0⟩ :: R)
      mem aw out σ k C) :
    (¬ (192 ≤ out.size ∧ allocationFits ptr ⟨384⟩) ∧
      RDrev (deployedRuntime v) g s0) ∨
    (192 ≤ out.size ∧ allocationFits ptr ⟨384⟩ ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨14858⟩
        (ptr :: ⟨160⟩ :: ⟨14943⟩ :: nextCursor ptr ⟨192⟩ :: ⟨15226⟩ ::
          ⟨15158⟩ :: ⟨12410⟩ :: id :: saved :: R)
        (marketReservedMem mem ptr) aw' out σ k' C') := by
  have h1 := metaMorphoV1_1_block_15129_fallthrough
    (immWords := wordsOf (immStore v)) (by omega) (by decide) rd
  have h2 := metaMorphoV1_1_block_15136_taken
    (immWords := wordsOf (immStore v)) (by omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  by_cases hlong : 192 ≤ out.size
  · have h3 := metaMorphoV1_1_block_15184_fallthrough
      (immWords := wordsOf (immStore v)) (by omega)
      (ugt_zero (by simpa only [UInt256.toNat_ofNat_of_lt hout] using hlong)) h2
    have h4 := metaMorphoV1_1_block_15208 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
    rcases marketReturnAllocationLong v (by simp only [List.length_cons]; omega) h4 with
      ⟨hbad, hrev⟩ | ⟨hfit, hdone⟩
    · exact .inl ⟨fun hc ↦ hbad hc.2, hrev⟩
    · exact .inr ⟨hlong, hfit, hdone⟩
  · have h3 := metaMorphoV1_1_block_15184_taken
      (immWords := wordsOf (immStore v)) (by omega)
      (by rw [ugt_one (by simpa only [UInt256.toNat_ofNat_of_lt hout] using
            Nat.lt_of_not_ge hlong)]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    exact .inl ⟨fun hc ↦ hlong hc.1, marketReturnAllocationShort v
      (by simp only [List.length_cons]; omega) (by omega) h3⟩

set_option maxRecDepth 2000 in
theorem accruedSupplyMarketRead {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr morpho saved id : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 15 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hlo : 96 ≤ ptr.toNat) (hptr : ptr.toNat < 2 ^ 64)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨15097⟩
      (⟨192⟩ :: morpho :: saved :: id :: ⟨0⟩ :: R) mem aw rdata σ k C) :
    (∃ evm' out ok, typedCallViaEVM config evm (AccountAddress.ofUInt256 morpho)
      "market" 0 [wordBytes32Value id] (ok, evm', out) false ∧
      (ok = false ∨ ¬ (MarketChecks out ∧ allocationFits ptr ⟨384⟩)) ∧
      RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      typedCallViaEVM config evm (AccountAddress.ofUInt256 morpho) "market" 0
        [wordBytes32Value id] (true, evm', out) false ∧
      SourceState s0 I evm'.accountMap evm' ∧ MarketChecks out ∧ out.size < 2 ^ 255 ∧
      allocationFits ptr ⟨384⟩ ∧
      memLoad ⟨64⟩ (marketReadMemory mem ptr id out) = nextCursor ptr ⟨384⟩ ∧
      (nextCursor ptr ⟨384⟩).toNat ≤ (marketReadMemory mem ptr id out).size ∧
      (∀ i, i < 6 → memLoad (nextCursor ptr ⟨192⟩ + UInt256.ofNat (32 * i))
        (marketReadMemory mem ptr id out) = calldataWord out (32 * i)) ∧
      MemoryPrefix mem (marketReadMemory mem ptr id out) ptr.toNat ∧
      RD (deployedRuntime v) I g s0 ⟨15141⟩
        (⟨15158⟩ :: saved :: id :: nextCursor ptr ⟨192⟩ :: R)
        (marketReadMemory mem ptr id out) aw' out evm'.accountMap k' C' := by
  have h4 : (ptr + UInt256.ofNat 4).toNat = ptr.toNat + 4 :=
    uadd_word_ofNat_toNat ptr 4 (by change _ < 2 ^ 256; omega)
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_15097_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) rd
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  simp only [metaMorphoV1_1_block_15097_stack, metaMorphoV1_1_block_15097_memory, hf, h4] at h1
  have hdec : decode (deployedRuntime v) ⟨15128⟩ = some (.STATICCALL, none) := by
    change decode (immutableLayout.runtime metaMorphoV1_1Bytecode
      (wordsOf (immStore v))) _ = _
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨15128⟩ : UInt256), UInt8.ofNat 250, .STATICCALL, none,
      immutableLayout_inBounds, immutableTemplate_size64)
  obtain ⟨evm', ok, out, aw2, k2, C2, hcall, hs', hout, h2⟩ :=
    typedStaticcallSimulation (by simp only [List.length_cons]; omega) hdec hs rfl
      (by change _ = some ((marketCallMem mem ptr.toNat id).readWithPadding ptr.toNat 36)
          rw [marketEncode, marketCallMem_read]) h1
  have hhi : out.size < 2 ^ 255 := lt_trans (marketReturnSize hcall) (by decide)
  cases ok with
  | false =>
      have h3 := metaMorphoV1_1_block_15129_taken
        (immWords := wordsOf (immStore v)) (by omega) (by decide)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
      exact .inl ⟨evm', out, false, hcall, .inl rfl,
        metaMorphoV1_1_block_15241 (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega)
          (by change 0 + (UInt256.ofNat out.size).toNat ≤ out.size
              rw [UInt256.toNat_ofNat_of_lt hout, Nat.zero_add]) h3⟩
  | true =>
      rcases accruedSupplyMarketAllocation v hstack hout h2 with
        ⟨hbad, hrev⟩ | ⟨hlong, hfit, aw3, k3, C3, h3⟩
      · exact .inl ⟨evm', out, true, hcall, .inr (fun hc ↦ hbad ⟨hc.1.1, hc.2⟩), hrev⟩
      · rcases marketReadDecode v (by simp only [List.length_cons]; omega) hlo hlong hout
            hfit (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h3 with
          ⟨hbad, hrev⟩ | ⟨hc, aw4, k4, C4, hfree', hsize', hfields, hprefix, h4⟩
        · exact .inl ⟨evm', out, true, hcall, .inr (fun hc ↦ hbad hc.1), hrev⟩
        · obtain ⟨aw5, k5, C5, h5⟩ := metaMorphoV1_1_block_15226_packed
            (immWords := wordsOf (immStore v)) (by omega)
            (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h4
          exact .inr ⟨evm', out, aw5, k5, C5, hcall, hs', hc, hhi, hfit,
            hfree', hsize', hfields, hprefix, h5⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
