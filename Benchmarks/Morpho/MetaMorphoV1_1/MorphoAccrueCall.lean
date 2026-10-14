import Benchmarks.Morpho.MetaMorphoV1_1.MorphoAccrueABI
import Benchmarks.Morpho.MetaMorphoV1_1.BorrowRateSetup
import Benchmarks.Morpho.MetaMorphoV1_1.ZeroCallSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_018
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_080
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_082

/-! Morpho interest accrual at the external boundary of the supply loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def morphoAccrueCallMem (mem : ByteArray) (ptr : Nat) (p : MarketParamsData) : ByteArray :=
  wordCallMemory mem ptr morphoAccrueSelectorWord p.words

def morphoAccrueReturnMem (mem : ByteArray) (ptr : UInt256) (p : MarketParamsData) : ByteArray :=
  writeWord (morphoAccrueCallMem mem ptr.toNat p) 64 ptr

theorem morphoAccrueCallMem_read (mem : ByteArray) (ptr : Nat) (p : MarketParamsData) :
    (morphoAccrueCallMem mem ptr p).readWithPadding ptr 164 = morphoAccrueCalldata p := by
  simpa only [MarketParamsData.words, List.length_cons, List.length_nil,
    show morphoAccrueSelectorWord.toByteArray.extract 0 4 = morphoAccrueSelector
      from by decide +kernel] using wordCallMemory_read mem ptr morphoAccrueSelectorWord p.words

theorem morphoAccrueReturnMem_free (mem : ByteArray) (ptr : UInt256) (p : MarketParamsData) :
    memLoad ⟨64⟩ (morphoAccrueReturnMem mem ptr p) = ptr :=
  loadedWord_of_read (by change 64 + 32 ≤ _; rw [morphoAccrueReturnMem, writeWord_sparse_size]; omega)
    (writeWord_sparse_read_back _ _ _)

theorem morphoAccrueReturnMem_prefix (mem : ByteArray) (ptr : UInt256) (p : MarketParamsData) :
    MemoryPrefix mem (morphoAccrueReturnMem mem ptr p) ptr.toNat :=
  (wordCallMemory_prefix _ _ _ _).trans
    (memoryPrefix_sparse_writeWord _ _ _ _ (.inr (by decide)))

set_option maxRecDepth 2000 in
theorem morphoAccrueReachCall {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params id cap i morpho : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 13 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hptr : ptr.toNat < 2 ^ 64)
    (hparamslo : 96 ≤ params.toNat) (hparams : params.toNat + 160 ≤ ptr.toNat)
    (hmem : params.toNat + 160 ≤ mem.size) (hloads : MarketParamsLoads mem params p)
    (rd : RD (deployedRuntime v) I g s0 ⟨18012⟩
      (id :: cap :: params :: i :: morpho :: R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C', RD (deployedRuntime v) I g s0 ⟨18046⟩
      (gasArg :: morpho :: ⟨0⟩ :: ptr :: ⟨164⟩ :: ptr :: ⟨0⟩ ::
        ptr :: id :: cap :: params :: i :: morpho :: R)
      (morphoAccrueCallMem mem ptr.toNat p) aw' rdata σ k' C' := by
  have hword : ptr.toNat + 164 < UInt256.size := by change _ < 2 ^ 256; omega
  have h4 : (ptr + UInt256.ofNat 4).toNat = ptr.toNat + 4 :=
    uadd_word_ofNat_toNat ptr 4 (by omega)
  have hp0 : MemoryPrefix mem (writeWord mem ptr.toNat morphoAccrueSelectorWord) ptr.toNat :=
    memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _))
  have hl0 := hloads.prefix hp0 hparamslo hmem hparams (by omega)
  obtain ⟨aw0, k0, C0, h0⟩ := metaMorphoV1_1_block_18012_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  simp only [metaMorphoV1_1_block_18012_stack, metaMorphoV1_1_block_18012_memory, hf] at h0
  obtain ⟨aw1, k1, C1, h1⟩ := marketParamsEncodeRoutine v p
    (by simp only [List.length_cons]; omega) (by have hm := hp0.size; omega)
    (by rw [h4]; omega) (by rw [h4]; omega) hl0
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h0
  rw [h4] at h1
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_18037_packed
    (immWords := wordsOf (immStore v)) hstack h1
  exact ⟨_, aw2, k2, C2, h2⟩

set_option maxRecDepth 2000 in
theorem morphoAccrueCallSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr gasArg : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (morpho : UInt256)
    (hstack : R.length + 8 ≤ 1024) (hs : SourceState s0 I σ evm)
    (hptr : ptr.toNat < 2 ^ 64)
    (rd : RD (deployedRuntime v) I g s0 ⟨18046⟩
      (gasArg :: morpho :: ⟨0⟩ :: ptr :: ⟨164⟩ :: ptr :: ⟨0⟩ :: ptr :: R)
      (morphoAccrueCallMem mem ptr.toNat p) aw rdata σ k C) :
    (∃ evm' out, typedCallViaEVM config evm (AccountAddress.ofUInt256 morpho)
      "accrueInterest" 0 [p.value] (false, evm', out) ∧ RDrev (deployedRuntime v) g s0) ∨
    ∃ (evm' : State) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      typedCallViaEVM config evm (AccountAddress.ofUInt256 morpho)
        "accrueInterest" 0 [p.value] (true, evm', out) ∧
      SourceState s0 I evm'.accountMap evm' ∧
      RD (deployedRuntime v) I g s0 ⟨18057⟩ (⟨0⟩ :: R)
        (morphoAccrueReturnMem mem ptr p) aw' out evm'.accountMap k' C' := by
  have hdec : decode (deployedRuntime v) ⟨18046⟩ = some (.CALL, none) := by
    change decode (immutableLayout.runtime metaMorphoV1_1Bytecode
      (wordsOf (immStore v))) _ = _
    immutable_decode(immutableLayout, metaMorphoV1_1Bytecode, wordsOf (immStore v),
      (⟨18046⟩ : UInt256), UInt8.ofNat 241, .CALL, none,
      immutableLayout_inBounds, immutableTemplate_size64)
  obtain ⟨evm', ok, out, aw1, k1, C1, hcall, hs', hout, h1⟩ :=
    typedZeroCallSimulation (by simp only [List.length_cons]; omega) hdec hs rfl
      (by change _ = some ((morphoAccrueCallMem mem ptr.toNat p).readWithPadding ptr.toNat 164)
          rw [morphoAccrueEncode p, morphoAccrueCallMem_read]) rd
  have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
    have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size := by
      change 0 ≤ (UInt256.ofNat out.size).toNat
      omega
    simp [min, hle]
  rw [hmin, byteArray_write_len_zero] at h1
  cases ok with
  | false =>
      have h2 := metaMorphoV1_1_block_18047_taken
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
      exact .inl ⟨evm', out, hcall, metaMorphoV1_1_block_2921
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by change 0 + (UInt256.ofNat out.size).toNat ≤ out.size
            rw [UInt256.toNat_ofNat_of_lt hout, Nat.zero_add]) h2⟩
  | true =>
      have h2 := metaMorphoV1_1_block_18047_fallthrough
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by decide) h1
      have h3 := metaMorphoV1_1_block_18053_taken
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
        (by decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
      have h4 := metaMorphoV1_1_block_18327 (immWords := wordsOf (immStore v))
        (by omega) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
      have hfit : allocationFits ptr ⟨0⟩ := by
        rw [allocationFits_aligned ptr ⟨0⟩ (by decide +kernel)]
        exact hptr
      obtain ⟨aw5, k5, C5, h5⟩ := allocateRoundedReturn v
        (by omega) hfit (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h4
      have hn : nextCursor ptr ⟨0⟩ = ptr := by
        rw [nextCursor, show roundedSize ⟨0⟩ = (⟨0⟩ : UInt256) from by decide +kernel,
          u256_add_zero]
      rw [hn] at h5
      obtain ⟨aw6, k6, C6, h6⟩ := metaMorphoV1_1_block_18337_packed
        (immWords := wordsOf (immStore v)) (by omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h5
      exact .inr ⟨evm', out, aw6, k6, C6, hcall, hs', h6⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
