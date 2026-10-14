import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateRowABI
import Benchmarks.Morpho.MetaMorphoV1_1.CalldataAddressRoutine
import Benchmarks.Morpho.MetaMorphoV1_1.StructReturnMemory
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_032

/-! The four address checks while materializing one reallocation row. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def reallocateRowFirstThreeMem (mem : ByteArray) (ptr : Nat) (row : ByteArray) : ByteArray :=
  wordSequenceMemory mem ptr [calldataWord row 0, calldataWord row 32, calldataWord row 64]

set_option maxRecDepth 2000 in
theorem reallocateRowFields {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {params allocation withdrawn base : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hin : base.toNat + 228 ≤ I.calldata.size)
    (hbase : base.toNat + 228 < UInt256.size) (hparams : params.toNat + 160 < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨6036⟩
      (params :: ⟨160⟩ :: allocation :: withdrawn :: base :: R) mem aw rdata σ k C) :
    (¬ MarketParamsChecks (reallocateRowBytes I.calldata (base.toNat + 36)) ∧
      RDrev (deployedRuntime v) g s0) ∨
    (MarketParamsChecks (reallocateRowBytes I.calldata (base.toNat + 36)) ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨6096⟩
        (calldataWord (reallocateRowBytes I.calldata (base.toNat + 36)) 96 ::
          params :: ⟨160⟩ :: allocation :: withdrawn :: base :: R)
        (reallocateRowFirstThreeMem mem params.toNat
          (reallocateRowBytes I.calldata (base.toNat + 36))) aw' rdata σ k' C') := by
  let row := reallocateRowBytes I.calldata (base.toNat + 36)
  have hrow : row.size = 192 := reallocateRowBytes_size (by omega)
  have hword (off : Nat) (hoff : off ≤ 160) :
      calldataWord I.calldata (base + UInt256.ofNat (36 + off)).toNat = calldataWord row off := by
    rw [uadd_word_ofNat_toNat base (36 + off) (by omega), ← Nat.add_assoc]
    exact (reallocateRowBytes_word (by omega) (by omega)).symm
  have hadd (off : Nat) (hoff : off ≤ 128) :
      (params + UInt256.ofNat off).toNat = params.toNat + off :=
    uadd_word_ofNat_toNat params off (by omega)
  have h0 := metaMorphoV1_1_block_6036 (immWords := wordsOf (immStore v))
    (by omega) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hc0 : (calldataWord row 0).toNat < EVM.addressModulus
  case neg =>
    exact .inl ⟨fun hc ↦ hc0 hc.2.1, decodeAddressAtRevert v
      (by simp only [List.length_cons]; omega)
      (by rw [hword 0 (by decide)]; exact hc0) h0⟩
  obtain ⟨k1, C1, r1⟩ := decodeAddressAt v
    (by simp only [List.length_cons]; omega)
    (by rw [hword 0 (by decide)]; exact hc0)
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h0
  simp only [hword 0 (by decide)] at r1
  obtain ⟨aw1, k1b, C1b, h1⟩ := metaMorphoV1_1_block_6048_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
  by_cases hc32 : (calldataWord row 32).toNat < EVM.addressModulus
  case neg =>
    exact .inl ⟨fun hc ↦ hc32 hc.2.2.1, decodeAddressAtRevert v
      (by simp only [List.length_cons]; omega)
      (by rw [hword 32 (by decide)]; exact hc32) h1⟩
  obtain ⟨k2, C2, r2⟩ := decodeAddressAt v
    (by simp only [List.length_cons]; omega)
    (by rw [hword 32 (by decide)]; exact hc32)
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  simp only [hword 32 (by decide)] at r2
  obtain ⟨aw2, k2b, C2b, h2⟩ := metaMorphoV1_1_block_6062_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
  by_cases hc64 : (calldataWord row 64).toNat < EVM.addressModulus
  case neg =>
    exact .inl ⟨fun hc ↦ hc64 hc.2.2.2.1, decodeAddressAtRevert v
      (by simp only [List.length_cons]; omega)
      (by rw [hword 64 (by decide)]; exact hc64) h2⟩
  obtain ⟨k3, C3, r3⟩ := decodeAddressAt v
    (by simp only [List.length_cons]; omega)
    (by rw [hword 64 (by decide)]; exact hc64)
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2
  simp only [hword 64 (by decide)] at r3
  obtain ⟨aw3, k3b, C3b, h3⟩ := metaMorphoV1_1_block_6079_packed
    (immWords := wordsOf (immStore v)) (by omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r3
  by_cases hc96 : (calldataWord row 96).toNat < EVM.addressModulus
  case neg =>
    exact .inl ⟨fun hc ↦ hc96 hc.2.2.2.2, decodeAddressAtRevert v
      (by simp only [List.length_cons]; omega)
      (by rw [hword 96 (by decide)]; exact hc96) h3⟩
  obtain ⟨k4, C4, r4⟩ := decodeAddressAt v
    (by simp only [List.length_cons]; omega)
    (by rw [hword 96 (by decide)]; exact hc96)
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h3
  simp only [hword 96 (by decide)] at r4
  refine .inr ⟨⟨by change 160 ≤ row.size; omega, hc0, hc32, hc64, hc96⟩, aw3, k4, C4, ?_⟩
  simpa only [metaMorphoV1_1_block_6048_memory, metaMorphoV1_1_block_6062_memory,
    metaMorphoV1_1_block_6079_memory, hadd 32 (by decide), hadd 64 (by decide),
    reallocateRowFirstThreeMem, wordSequenceMemory, Nat.add_zero, Nat.add_assoc,
    Nat.reduceAdd] using r4

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
