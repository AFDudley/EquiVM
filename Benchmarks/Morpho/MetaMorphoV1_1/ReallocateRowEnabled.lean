import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateRowMemory
import Benchmarks.Morpho.MetaMorphoV1_1.SetCapEntryRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_034

/-! Complete the row copy, hash its market parameters, and check its enabled flag. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem reallocateRowEnabled {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {params allocation withdrawn base : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hin : base.toNat + 228 ≤ I.calldata.size)
    (hbase : base.toNat + 228 < UInt256.size)
    (hsep : allocation.toNat + 64 ≤ params.toNat) (hparams : params.toNat + 160 < UInt256.size)
    (hc : MarketParamsChecks (reallocateRowBytes I.calldata (base.toNat + 36)))
    (rd : RD (deployedRuntime v) I g s0 ⟨6096⟩
      (calldataWord (reallocateRowBytes I.calldata (base.toNat + 36)) 96 ::
        params :: ⟨160⟩ :: allocation :: withdrawn :: base :: R)
      (reallocateRowFirstThreeMem mem params.toNat
        (reallocateRowBytes I.calldata (base.toNat + 36))) aw rdata σ k C) :
    (setCapEnabledWord I σ (marketParamsData (reallocateRowBytes I.calldata (base.toNat + 36))).id = ⟨0⟩ ∧
      RDrev (deployedRuntime v) g s0) ∨
    (setCapEnabledWord I σ (marketParamsData (reallocateRowBytes I.calldata (base.toNat + 36))).id ≠ ⟨0⟩ ∧
      ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨6152⟩
        ((allocation + ⟨32⟩) :: allocation :: withdrawn ::
          (marketParamsData (reallocateRowBytes I.calldata (base.toNat + 36))).id :: R)
        (reallocateRowMemory mem allocation params
          (reallocateRowBytes I.calldata (base.toNat + 36))) aw' rdata σ k' C') := by
  let row := reallocateRowBytes I.calldata (base.toNat + 36)
  have hword (off : Nat) (hoff : off ≤ 160) :
      calldataWord I.calldata (base + UInt256.ofNat (36 + off)).toNat = calldataWord row off := by
    rw [uadd_word_ofNat_toNat base (36 + off) (by omega), ← Nat.add_assoc]
    exact (reallocateRowBytes_word (by omega) (by omega)).symm
  have hadd (off : Nat) (hoff : off ≤ 128) :
      (params + UInt256.ofNat off).toNat = params.toNat + off :=
    uadd_word_ofNat_toNat params off (by omega)
  have ha32 : (allocation + UInt256.ofNat 32).toNat = allocation.toNat + 32 :=
    uadd_word_ofNat_toNat allocation 32 (by omega)
  have hwrite (m : ByteArray) (off : Nat) (w : UInt256) :
      w.toByteArray.write 0 m off 32 = writeWord m off w := rfl
  have hread (off : Nat) : uInt256OfByteArray (I.calldata.readBytes off 32) =
      calldataWord I.calldata off := rfl
  have hm : writeWord (writeWord (writeWord (writeWord
      (reallocateRowFirstThreeMem mem params.toNat row) (params + UInt256.ofNat 96).toNat
        (calldataWord row 96)) (params + UInt256.ofNat 128).toNat
          (calldataWord I.calldata (base + UInt256.ofNat 164).toNat)) allocation.toNat params)
            (allocation + UInt256.ofNat 32).toNat
              (calldataWord I.calldata (base + UInt256.ofNat 196).toNat) =
      reallocateRowStructMem mem allocation params row := by
    simp only [hword 128 (by decide), hword 160 (by decide), hadd 96 (by decide),
      hadd 128 (by decide), ha32, reallocateRowFirstThreeMem, reallocateRowStructMem,
      marketParamsCopyMem, structReturnMemory, wordArrayWords, wordSequenceMemory,
      Nat.reduceAdd, Nat.reduceMul, Nat.add_zero, Nat.add_assoc]
  have hh := reallocateRowStructMem_hash (mem := mem) hc hsep hparams
  have hmap : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (writeWord (writeWord (reallocateRowStructMem mem allocation params row) 0
        (marketParamsData row).id) 32 ⟨13⟩) = solcMappingSlot ⟨13⟩ (marketParamsData row).id :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  dsimp only [row] at hm hmap
  by_cases hz : setCapEnabledWord I σ (marketParamsData row).id = ⟨0⟩
  · have hg : UInt256.isZero (setCapEnabledWord I σ (marketParamsData row).id) ≠ UInt256.ofNat 0 := by
      rw [hz]; decide
    obtain ⟨k1, C1, h1⟩ := metaMorphoV1_1_block_6096_taken
      (immWords := wordsOf (immStore v)) hstack (by
        simp only [hread, hwrite, hm, hh,
          show (⟨0⟩ : UInt256).toNat = 0 from rfl,
          show (UInt256.ofNat 32).toNat = 32 from rfl,
          show UInt256.ofNat 13 = (⟨13⟩ : UInt256) from rfl, hmap]
        exact hg)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact .inl ⟨hz, metaMorphoV1_1_block_6770 (immWords := wordsOf (immStore v)) (by omega) h1⟩
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_6096_fallthrough_packed
      (immWords := wordsOf (immStore v)) hstack (by
        simp only [hread, hwrite, hm, hh,
          show (⟨0⟩ : UInt256).toNat = 0 from rfl,
          show (UInt256.ofNat 32).toNat = 32 from rfl,
          show UInt256.ofNat 13 = (⟨13⟩ : UInt256) from rfl, hmap]
        exact isZero_eq_zero_of_ne hz) rd
    refine .inr ⟨hz, aw1, k1, C1, ?_⟩
    simpa only [metaMorphoV1_1_block_6096_fallthrough_stack,
      metaMorphoV1_1_block_6096_fallthrough_memory, hread, hwrite, hm, hh, reallocateRowMemory,
      twoWordHashMem, wordAt0Mem] using h1

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
