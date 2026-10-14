import Benchmarks.Morpho.MetaMorphoV1_1.MorphoWithdrawABI
import Benchmarks.Morpho.MetaMorphoV1_1.BorrowRateSetup
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_084

/-! The withdrawal call buffer assembled from a decoded market-parameters struct. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def morphoWithdrawCallMem (mem : ByteArray) (ptr : Nat) (p : MarketParamsData)
    (amount : UInt256) (sender : AccountAddress) : ByteArray :=
  wordCallMemory mem ptr morphoWithdrawSelectorWord (morphoWithdrawWords p amount ⟨0⟩ sender sender)

theorem morphoWithdrawCallMem_read (mem : ByteArray) (ptr : Nat) (p : MarketParamsData)
    (amount : UInt256) (sender : AccountAddress) :
    (morphoWithdrawCallMem mem ptr p amount sender).readWithPadding ptr 292 =
      morphoWithdrawCalldata p amount ⟨0⟩ sender sender := by
  simpa only [morphoWithdrawWords, MarketParamsData.words, List.length_append,
    List.length_cons, List.length_nil,
    show morphoWithdrawSelectorWord.toByteArray.extract 0 4 = morphoWithdrawSelector
      from by decide +kernel] using
    wordCallMemory_read mem ptr morphoWithdrawSelectorWord (morphoWithdrawWords p amount ⟨0⟩ sender sender)

theorem morphoWithdrawCallMem_size (mem : ByteArray) (ptr : Nat) (p : MarketParamsData)
    (amount : UInt256) (sender : AccountAddress) :
    (morphoWithdrawCallMem mem ptr p amount sender).size = max mem.size (ptr + 292) := by
  rw [morphoWithdrawCallMem, wordCallMemory_size _ _ _ (by simp [morphoWithdrawWords, MarketParamsData.words])]
  simp only [morphoWithdrawWords, MarketParamsData.words, List.length_append,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc]

set_option maxRecDepth 2000 in
theorem morphoWithdrawReachCall {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params amount : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 10 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hptr : ptr.toNat < 2 ^ 64)
    (hparamslo : 96 ≤ params.toNat) (hparams : params.toNat + 160 ≤ ptr.toNat)
    (hmem : params.toNat + 160 ≤ mem.size) (hloads : MarketParamsLoads mem params p)
    (rd : RD (deployedRuntime v) I g s0 ⟨18776⟩
      (params :: amount :: R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C', RD (deployedRuntime v) I g s0 ⟨18880⟩
      (gasArg :: UInt256.ofNat v.MORPHO.toNat :: ⟨0⟩ :: ptr :: ⟨292⟩ :: ptr :: ⟨64⟩ ::
        ptr :: amount :: R)
      (morphoWithdrawCallMem mem ptr.toNat p amount I.codeOwner) aw' rdata σ k' C' := by
  have hword : ptr.toNat + 292 < UInt256.size := by change _ < 2 ^ 256; omega
  have hadd (n : Nat) (hn : n ≤ 260) : (ptr + UInt256.ofNat n).toNat = ptr.toNat + n :=
    uadd_word_ofNat_toNat ptr n (by omega)
  have hp0 : MemoryPrefix mem (writeWord mem ptr.toNat morphoWithdrawSelectorWord) ptr.toNat :=
    memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _))
  have hl0 := hloads.prefix hp0 hparamslo hmem hparams (by omega)
  obtain ⟨aw0, k0, C0, h0⟩ := metaMorphoV1_1_block_18776_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  simp only [metaMorphoV1_1_block_18776_stack, metaMorphoV1_1_block_18776_memory, hf] at h0
  obtain ⟨aw1, k1, C1, h1⟩ := marketParamsEncodeRoutine v p
    (by simp only [List.length_cons]; omega) (by have hm := hp0.size; omega)
    (by rw [hadd 4 (by decide)]; omega) (by rw [hadd 4 (by decide)]; omega) hl0
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h0
  rw [hadd 4 (by decide)] at h1
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_18804_packed
    (immWords := wordsOf (immStore v)) hstack h1
  have hm : metaMorphoV1_1_block_18804_memory (ee := I)
      (mem := wordSequenceMemory (writeWord mem ptr.toNat morphoWithdrawSelectorWord)
        (ptr.toNat + 4) p.words) (x0 := ptr) (x1 := amount) =
      morphoWithdrawCallMem mem ptr.toNat p amount I.codeOwner := by
    simp only [metaMorphoV1_1_block_18804_memory, hadd 164 (by decide), hadd 196 (by decide),
      hadd 228 (by decide), hadd 260 (by decide), morphoWithdrawCallMem, wordCallMemory,
      morphoWithdrawWords, MarketParamsData.words, List.cons_append, List.nil_append,
      wordSequenceMemory, Nat.add_assoc, Nat.reduceAdd]
    rfl
  have hmask : UInt256.land (wordsOf (immStore v) "MORPHO")
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = UInt256.ofNat v.MORPHO.toNat := by
    rw [wordsOf_immStore_MORPHO]
    exact solcAddrMask_clean (addressWord_val_canonical v.MORPHO)
  simp only [metaMorphoV1_1_block_18804_stack, hmask, hm] at h2
  exact ⟨_, aw2, k2, C2, h2⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
