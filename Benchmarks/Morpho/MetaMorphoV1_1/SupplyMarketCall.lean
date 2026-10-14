import Benchmarks.Morpho.MetaMorphoV1_1.MarketCall
import Benchmarks.Morpho.MetaMorphoV1_1.MarketReturnAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_080
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_082

/-! The supply loop's market call and its shared return-buffer allocator. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem supplyMarketReachStaticcall {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr id cap params i morpho : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 12 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hptr : ptr.toNat < 2 ^ 64)
    (rd : RD (deployedRuntime v) I g s0 ⟨18057⟩
      (⟨0⟩ :: id :: cap :: params :: i :: morpho :: R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C', RD (deployedRuntime v) I g s0 ⟨18088⟩
      (gasArg :: morpho :: ptr :: ⟨36⟩ :: ptr :: ⟨192⟩ ::
        id :: ptr :: cap :: params :: i :: morpho :: R)
      (marketCallMem mem ptr.toNat id) aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', h⟩ := metaMorphoV1_1_block_18057_packed
    (immWords := wordsOf (immStore v)) hstack rd
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  have h4 : (ptr + UInt256.ofNat 4).toNat = ptr.toNat + 4 :=
    uadd_word_ofNat_toNat ptr 4 (by change _ < 2 ^ 256; omega)
  simp only [metaMorphoV1_1_block_18057_stack, metaMorphoV1_1_block_18057_memory,
    hf, h4] at h
  exact ⟨_, aw', k', C', h⟩

theorem supplyMarketStaticcall {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr id morpho gasArg : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 3 ≤ 1024)
    (hs : SourceState s0 I σ evm)
    (rd : RD (deployedRuntime v) I g s0 ⟨18088⟩
      (gasArg :: morpho :: ptr :: ⟨36⟩ :: ptr :: ⟨192⟩ :: id :: ptr :: R)
      (marketCallMem mem ptr.toNat id) aw rdata σ k C) :
    ∃ (evm' : State) (ok : Bool) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      typedCallViaEVM config evm (AccountAddress.ofUInt256 morpho) "market" 0
        [wordBytes32Value id] (ok, evm', out) false ∧
      SourceState s0 I evm'.accountMap evm' ∧ out.size < UInt256.size ∧
      RD (deployedRuntime v) I g s0 ⟨18089⟩
        ((if ok then ⟨1⟩ else ⟨0⟩) :: id :: ptr :: R)
        (marketOutputMem (marketCallMem mem ptr.toNat id) ptr out)
        aw' out evm'.accountMap k' C' := by
  have hdec : decode (deployedRuntime v) ⟨18088⟩ = some (.STATICCALL, none) := by
    change decode (immutableLayout.runtime metaMorphoV1_1Bytecode
      (wordsOf (immStore v))) _ = _
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨18088⟩ : UInt256), UInt8.ofNat 250, .STATICCALL, none,
      immutableLayout_inBounds, immutableTemplate_size64)
  exact typedStaticcallSimulation (by simpa only [List.length_cons] using hstack)
    hdec hs rfl (by change _ = some ((marketCallMem mem ptr.toNat id).readWithPadding
      ptr.toNat 36); rw [marketEncode, marketCallMem_read]) rd

set_option maxRecDepth 2000 in
theorem supplyMarketCallFailure {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr id : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hout : out.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨18089⟩ (⟨0⟩ :: id :: ptr :: R)
      mem aw out σ k C) : RDrev (deployedRuntime v) g s0 := by
  have h1 := metaMorphoV1_1_block_18089_taken (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1_block_2921 (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1_block_18089_taken_stack, List.length_cons]; omega)
    (by change 0 + (UInt256.ofNat out.size).toNat ≤ out.size
        rw [UInt256.toNat_ofNat_of_lt hout, Nat.zero_add]) h1

set_option maxRecDepth 2000 in
theorem supplyMarketReturnAllocation {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr id : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 14 ≤ 1024)
    (hout : out.size < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨18089⟩ (⟨1⟩ :: id :: ptr :: R)
      mem aw out σ k C) :
    (¬ (192 ≤ out.size ∧ allocationFits ptr ⟨384⟩) ∧
      RDrev (deployedRuntime v) g s0) ∨
    (192 ≤ out.size ∧ allocationFits ptr ⟨384⟩ ∧ ∃ aw' k' C',
      RD (deployedRuntime v) I g s0 ⟨14858⟩
        (ptr :: ⟨160⟩ :: ⟨14943⟩ :: nextCursor ptr ⟨192⟩ :: ⟨18320⟩ ::
          ⟨18119⟩ :: id :: ⟨18144⟩ :: R)
        (marketReservedMem mem ptr) aw' out σ k' C') := by
  have h1 := metaMorphoV1_1_block_18089_fallthrough
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) (by decide) rd
  have h2 := metaMorphoV1_1_block_18096_taken
    (immWords := wordsOf (immStore v)) (by omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  by_cases hlong : 192 ≤ out.size
  · have h3 := metaMorphoV1_1_block_18291_fallthrough
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (ugt_zero (by simpa only [UInt256.toNat_ofNat_of_lt hout] using hlong)) h2
    have h4 := metaMorphoV1_1_block_18311 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
    rcases marketReturnAllocationLong v (by simp only [List.length_cons]; omega) h4 with
      ⟨hbad, hrev⟩ | ⟨hfit, hdone⟩
    · exact .inl ⟨fun hc ↦ hbad hc.2, hrev⟩
    · exact .inr ⟨hlong, hfit, hdone⟩
  · have h3 := metaMorphoV1_1_block_18291_taken
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [ugt_one (by simpa only [UInt256.toNat_ofNat_of_lt hout] using
            Nat.lt_of_not_ge hlong)]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    exact .inl ⟨fun hc ↦ hlong hc.1, marketReturnAllocationShort v
      (by simp only [List.length_cons]; omega) (by omega) h3⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
