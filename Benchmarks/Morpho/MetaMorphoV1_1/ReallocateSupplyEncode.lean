import Benchmarks.Morpho.MetaMorphoV1_1.MorphoSupplyEncode
import Benchmarks.Morpho.MetaMorphoV1_1.BorrowRateSetup
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_033

/-! Call-buffer setup for the strict supply in reallocation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem reallocateSupplyReachCall {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr params allocation amount id : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (p : MarketParamsData) (hstack : R.length + 18 ≤ 1024)
    (halloc : memLoad allocation mem = params)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hptr : ptr.toNat < 2 ^ 64)
    (hparamslo : 96 ≤ params.toNat) (hparams : params.toNat + 160 ≤ ptr.toNat)
    (hmem : params.toNat + 160 ≤ mem.size) (hloads : MarketParamsLoads mem params p)
    (rd : RD (deployedRuntime v) I g s0 ⟨6526⟩
      (allocation :: id :: amount :: R) mem aw rdata σ k C) :
    ∃ gasArg aw' k' C', RD (deployedRuntime v) I g s0 ⟨6609⟩
      (gasArg :: UInt256.ofNat v.MORPHO.toNat :: ⟨0⟩ :: ptr :: ⟨324⟩ :: ptr :: ⟨64⟩ ::
        id :: amount :: ptr :: R)
      (morphoSupplyCallMem mem ptr.toNat p amount I.codeOwner) aw' rdata σ k' C' := by
  have hword : ptr.toNat + 324 < UInt256.size := by change _ < 2 ^ 256; omega
  have h4 : (ptr + UInt256.ofNat 4).toNat = ptr.toNat + 4 :=
    uadd_word_ofNat_toNat ptr 4 (by omega)
  have hp0 : MemoryPrefix mem (writeWord mem ptr.toNat morphoSupplySelectorWord) ptr.toNat :=
    memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _))
  have hl0 := hloads.prefix hp0 hparamslo hmem hparams (by omega)
  obtain ⟨aw0, k0, C0, h0⟩ := metaMorphoV1_1_block_6526_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have hf : memLoad (UInt256.ofNat 64) mem = ptr := hfree
  simp only [metaMorphoV1_1_block_6526_stack, metaMorphoV1_1_block_6526_memory, hf, halloc] at h0
  obtain ⟨aw1, k1, C1, h1⟩ := morphoSupplyEncodeRoutine v p I.codeOwner
    (by simp only [List.length_cons]; omega) (by have hm := hp0.size; omega)
    (by rw [h4]; omega) (by rw [h4]; omega) hl0
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h0
  rw [h4] at h1
  obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_6562_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) h1
  have he : UInt256.sub ((ptr + UInt256.ofNat 4) + ⟨320⟩) ptr = ⟨324⟩ := by
    rw [u256_add_assoc, word_add_sub_left]
    rfl
  have hmask : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) (wordsOf (immStore v) "MORPHO") = UInt256.ofNat v.MORPHO.toNat := by
    rw [wordsOf_immStore_MORPHO]
    exact solcAddrMask_clean_left (addressWord_val_canonical v.MORPHO)
  simp only [metaMorphoV1_1_block_6562_stack, he, hmask] at h2
  exact ⟨_, aw2, k2, C2, h2⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
