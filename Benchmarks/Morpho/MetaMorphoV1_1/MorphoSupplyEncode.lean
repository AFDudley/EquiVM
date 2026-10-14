import Benchmarks.Morpho.MetaMorphoV1_1.MorphoSupplyABI
import Benchmarks.Morpho.MetaMorphoV1_1.BorrowRateSetup
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_081

/-! The shared supply-call encoder and the supply loop's call-buffer setup. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def morphoSupplyCallMem (mem : ByteArray) (ptr : Nat) (p : MarketParamsData)
    (amount : UInt256) (sender : AccountAddress) : ByteArray :=
  wordCallMemory mem ptr morphoSupplySelectorWord (morphoSupplyWords p amount sender)

theorem morphoSupplyCallMem_read (mem : ByteArray) (ptr : Nat) (p : MarketParamsData)
    (amount : UInt256) (sender : AccountAddress) :
    (morphoSupplyCallMem mem ptr p amount sender).readWithPadding ptr 324 =
      morphoSupplyCalldata p amount sender := by
  simpa only [morphoSupplyWords, MarketParamsData.words, List.length_append,
    List.length_cons, List.length_nil,
    show morphoSupplySelectorWord.toByteArray.extract 0 4 = morphoSupplySelector
      from by decide +kernel] using
    wordCallMemory_read mem ptr morphoSupplySelectorWord (morphoSupplyWords p amount sender)

theorem morphoSupplyCallMem_size (mem : ByteArray) (ptr : Nat) (p : MarketParamsData)
    (amount : UInt256) (sender : AccountAddress) :
    (morphoSupplyCallMem mem ptr p amount sender).size = max mem.size (ptr + 324) := by
  rw [morphoSupplyCallMem, wordCallMemory_size _ _ _ (by simp [morphoSupplyWords, MarketParamsData.words])]
  simp only [morphoSupplyWords, MarketParamsData.words, List.length_append,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul, Nat.add_assoc]

-- GENERALIZES the compiler's encoder at 12175 to arbitrary continuations and market data.
set_option maxRecDepth 2000 in
theorem morphoSupplyEncodeRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {src dst amount ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (sender : AccountAddress)
    (hstack : R.length + 12 ≤ 1024)
    (hmem : src.toNat + 160 ≤ mem.size) (hsep : src.toNat + 160 ≤ dst.toNat)
    (hdst : dst.toNat + 320 < UInt256.size) (hloads : MarketParamsLoads mem src p)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨12175⟩
      (dst :: src :: amount :: UInt256.ofNat sender.toNat :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret ((dst + ⟨320⟩) :: R)
      (wordSequenceMemory mem dst.toNat (morphoSupplyWords p amount sender))
      aw' rdata σ k' C' := by
  have h1 := metaMorphoV1_1_block_12175 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨aw2, k2, C2, h2⟩ := marketParamsEncodeRoutine v p
    (by simp only [List.length_cons]; omega) hmem hsep (by omega) hloads
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_12190_packed
    (immWords := wordsOf (immStore v)) (by omega) hret h2
  have hadd (n : Nat) (hn : n ≤ 288) : (dst + UInt256.ofNat n).toNat = dst.toNat + n :=
    uadd_word_ofNat_toNat dst n (by omega)
  have hmask : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) (UInt256.ofNat sender.toNat) = UInt256.ofNat sender.toNat :=
    solcAddrMask_clean_left (addressWord_val_canonical sender)
  have hm : metaMorphoV1_1_block_12190_memory
      (mem := wordSequenceMemory mem dst.toNat p.words)
      (x0 := amount) (x1 := UInt256.ofNat sender.toNat) (x2 := dst) =
      wordSequenceMemory mem dst.toNat (morphoSupplyWords p amount sender) := by
    simp only [metaMorphoV1_1_block_12190_memory, hmask, hadd 160 (by decide),
      hadd 192 (by decide), hadd 224 (by decide), hadd 256 (by decide), hadd 288 (by decide),
      morphoSupplyWords, MarketParamsData.words, List.cons_append, List.nil_append,
      wordSequenceMemory, Nat.add_assoc, Nat.reduceAdd]
    rfl
  simp only [metaMorphoV1_1_block_12190_stack, hm] at h3
  exact ⟨aw3, k3, C3, h3⟩

set_option maxRecDepth 2000 in
theorem morphoSupplyReachCall {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params amount i morpho assets : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 20 ≤ 1024)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hptr : ptr.toNat < 2 ^ 64)
    (hparamslo : 96 ≤ params.toNat) (hparams : params.toNat + 160 ≤ ptr.toNat)
    (hmem : params.toNat + 160 ≤ mem.size) (hloads : MarketParamsLoads mem params p)
    (rd : RD (deployedRuntime v) I g s0 ⟨18186⟩
      (params :: amount :: i :: morpho :: assets :: R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C', RD (deployedRuntime v) I g s0 ⟨18226⟩
      (gasArg :: morpho :: ⟨0⟩ :: ptr :: ⟨324⟩ :: ptr :: ⟨64⟩ ::
        ptr :: amount :: i :: morpho :: assets :: R)
      (morphoSupplyCallMem mem ptr.toNat p amount I.codeOwner) aw' rdata σ k' C' := by
  have hword : ptr.toNat + 324 < UInt256.size := by change _ < 2 ^ 256; omega
  have h4 : (ptr + UInt256.ofNat 4).toNat = ptr.toNat + 4 :=
    uadd_word_ofNat_toNat ptr 4 (by omega)
  have hp0 : MemoryPrefix mem (writeWord mem ptr.toNat morphoSupplySelectorWord) ptr.toNat :=
    memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _))
  have hl0 := hloads.prefix hp0 hparamslo hmem hparams (by omega)
  obtain ⟨aw0, k0, C0, h0⟩ := metaMorphoV1_1_block_18186_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  simp only [metaMorphoV1_1_block_18186_stack, metaMorphoV1_1_block_18186_memory, hf] at h0
  obtain ⟨aw1, k1, C1, h1⟩ := morphoSupplyEncodeRoutine v p I.codeOwner
    (by simp only [List.length_cons]; omega) (by have hm := hp0.size; omega)
    (by rw [h4]; omega) (by rw [h4]; omega) hl0
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h0
  rw [h4] at h1
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_18220_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) h1
  have he : UInt256.sub ((ptr + UInt256.ofNat 4) + ⟨320⟩) ptr = ⟨324⟩ := by
    rw [u256_add_assoc, word_add_sub_left]
    rfl
  simp only [metaMorphoV1_1_block_18220_stack, he] at h2
  exact ⟨_, aw2, k2, C2, h2⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
