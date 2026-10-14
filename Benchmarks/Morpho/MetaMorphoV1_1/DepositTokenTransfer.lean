import Benchmarks.Morpho.MetaMorphoV1_1.SafeTransferFromSource
import Benchmarks.Morpho.MetaMorphoV1_1.OptionalCallRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_068

/-! Deposit's transferFrom call, including request and return-data allocation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

def depositEventTopic : UInt256 :=
  ⟨99841187323991878651857463966695491112958443285409756881630392772141504727511⟩

def depositAfterTransferStack (caller receiver : AccountAddress) (assets shares : UInt256)
    (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat receiver.toNat, ⟨64⟩, depositEventTopic, UInt256.ofNat caller.toNat,
    shares, assets, ⟨13745⟩, ⟨14753⟩] ++ R

theorem depositTokenTransferSimulation {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {ptr : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (caller receiver : AccountAddress) (assets shares : UInt256)
    (hstack : R.length + 21 ≤ 1024) (hs : SourceState s0 I σ evm)
    (hptr : ptr.toNat < 2 ^ 64) (hlo : 128 ≤ ptr.toNat) (hsize : 128 ≤ mem.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (rd : RD (deployedRuntime v) I g s0 ⟨14558⟩
      ([UInt256.ofNat caller.toNat, UInt256.ofNat receiver.toNat, assets, shares] ++ R)
      mem aw rdata σ k C) :
    (ExecFuncBody config (safeTransferFromFrame (immStore v) v._asset caller I.codeOwner assets ptr)
        evm allocatedSafeTransferFromFunction.body .reverted ∧ RDrev (deployedRuntime v) g s0) ∨
      ∃ (evm' : State) (cursor : UInt256) (mem' out : ByteArray) (aw' : UInt256) (k' C' : Nat),
        SourceState s0 I evm'.accountMap evm' ∧
        ExecFuncBody config (safeTransferFromFrame (immStore v) v._asset caller I.codeOwner assets ptr)
          evm allocatedSafeTransferFromFunction.body
          (.returned (safeTransferFromResultFrame (immStore v) v._asset caller I.codeOwner
            assets ptr cursor) evm' (some [uint256Value cursor])) ∧
        cursor.toNat < 2 ^ 64 ∧ ptr.toNat ≤ cursor.toNat ∧ MemoryPrefix mem mem' ptr.toNat ∧
        memLoad ⟨64⟩ mem' = cursor ∧
        RD (deployedRuntime v) I g s0 ⟨14702⟩
          (depositAfterTransferStack caller receiver assets shares R) mem' aw' out
          evm'.accountMap k' C' := by
  simp only [List.cons_append, List.nil_append] at rd
  have h32 := uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)
  have h36 := uadd_word_ofNat_toNat ptr 36 (by change _ < 2 ^ 256; omega)
  have h68 := uadd_word_ofNat_toNat ptr 68 (by change _ < 2 ^ 256; omega)
  have h100 := uadd_word_ofNat_toNat ptr 100 (by change _ < 2 ^ 256; omega)
  have hmask : UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 160)) (UInt256.ofNat 1)) (UInt256.ofNat caller.toNat) =
      UInt256.ofNat caller.toNat := easWord_mask caller
  change memLoad (UInt256.ofNat 64) mem = ptr at hfree
  have hmem : metaMorphoV1_1_block_14558_memory (ee := I) (mem := mem)
      (x0 := UInt256.ofNat caller.toNat) (x2 := assets) =
      encodedWordCallMemory mem ptr safeTransferFromSelectorWord
        (safeTransferFromWords caller I.codeOwner assets) := by
    simp only [metaMorphoV1_1_block_14558_memory, hfree, hmask, h32, h36, h68, h100,
      encodedWordCallMemory, wordCallMemory, wordSequenceMemory, safeTransferFromWords,
      safeTransferFromSelectorWord, Reasoning.Theory.writeWord,
      show ptr.toNat + 32 + 4 = ptr.toNat + 36 from by omega,
      show ptr.toNat + 36 + 32 = ptr.toNat + 68 from by omega,
      show ptr.toNat + 68 + 32 = ptr.toNat + 100 from by omega]
    rfl
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_14558_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [metaMorphoV1_1_block_14558_stack, hfree, hmask, hmem] at h1
  by_cases hfit : allocationFits ptr ⟨132⟩
  · obtain ⟨aw2, k2, C2, h2⟩ := allocateRoundedReturn v
      (by simp only [List.length_cons]; omega) hfit
      (by change (D_J (immutableLayout.runtime metaMorphoV1_1Bytecode
            (wordsOf (immStore v))) 0).contains _ = true
          rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
    have h3 := metaMorphoV1_1_block_14664 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    simp only [metaMorphoV1_1_block_14664_stack, wordsOf_immStore__asset] at h3
    let cm := allocatedWordCallMemory mem ptr safeTransferFromSelectorWord
      (safeTransferFromWords caller I.codeOwner assets)
    have hpre : MemoryPrefix mem cm ptr.toNat := allocatedWordCallMemory_prefix _ _ _ _
    have hz : memLoad ⟨96⟩ cm = ⟨0⟩ :=
      (hpre.load_preserved (by decide : 96 ≤ 96) hlo hsize (by decide)).trans hzero
    rcases optionalCallSimulation (data := safeTransferFromCalldata caller I.codeOwner assets)
      v (immStore v) v._asset (by simp only [List.length_cons]; omega) hs
      hfit.1 (by have := hfit.2; omega) (by rw [safeTransferFromCalldata_size]; decide)
      (allocatedWordCallMemory_free mem ptr safeTransferFromSelectorWord
        (safeTransferFromWords caller I.codeOwner assets)) hz
      (by
        simpa only [safeTransferFromCalldata_size] using
          allocatedWordCallMemory_length mem ptr safeTransferFromSelectorWord
            (words := safeTransferFromWords caller I.codeOwner assets)
            (by simp [safeTransferFromWords]) (by omega))
      (by simpa only [safeTransferFromCalldata_size] using
        safeTransferFromMemory_read mem ptr caller I.codeOwner assets (by omega) hptr)
      (by change (D_J (immutableLayout.runtime metaMorphoV1_1Bytecode
            (wordsOf (immStore v))) 0).contains _ = true
          rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3 with
      ⟨hsource, hrev⟩ | ⟨evm', out, aw3, k3, C3, hs', hout, hsource, hpref, hfree', h4⟩
    · exact .inl ⟨safeTransferFromBodyRevertsCall evm (immStore v) v._asset caller
        I.codeOwner assets ptr hfit hsource, hrev⟩
    · have hc := callReturnCursor_bound (nextCursor ptr ⟨132⟩) out hfit.1 hout
      exact .inr ⟨evm', _, _, out, aw3, k3, C3, hs',
        safeTransferFromBodyReturns (immStore v) v._asset caller I.codeOwner assets ptr _ hfit hsource,
        hc.1, le_trans hfit.2 hc.2, hpre.trans (hpref.mono hfit.2), hfree', h4⟩
  · exact .inl ⟨safeTransferFromBodyRevertsAllocation evm (immStore v) v._asset caller
      I.codeOwner assets ptr hfit,
      allocateRoundedRevert v (by simp only [List.length_cons]; omega) hfit h1⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
