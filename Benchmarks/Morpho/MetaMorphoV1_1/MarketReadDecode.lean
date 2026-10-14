import Benchmarks.Morpho.MetaMorphoV1_1.MarketDecodeRoutines

/-! The shared market decoder, retaining its memory representation at any continuation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

-- GENERALIZES marketReadSimulation's decoder to every caller of the shared routine.
set_option maxRecDepth 2000 in
theorem marketReadDecode {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap}
    {k C : Nat} {ptr id ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 11 ≤ 1024)
    (hlo : 96 ≤ ptr.toNat) (hlong : 192 ≤ out.size) (hout : out.size < UInt256.size)
    (hfit : allocationFits ptr ⟨384⟩)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨14858⟩
      (ptr :: ⟨160⟩ :: ⟨14943⟩ :: nextCursor ptr ⟨192⟩ :: ret :: R)
      (marketReservedMem (marketOutputMem (marketCallMem mem ptr.toNat id) ptr out) ptr)
      aw out σ k C) :
    (¬ MarketChecks out ∧ RDrev (deployedRuntime v) g s0) ∨
    (MarketChecks out ∧ ∃ aw' k' C',
      memLoad ⟨64⟩ (marketReadMemory mem ptr id out) = nextCursor ptr ⟨384⟩ ∧
      (nextCursor ptr ⟨384⟩).toNat ≤ (marketReadMemory mem ptr id out).size ∧
      (∀ i, i < 6 → memLoad (nextCursor ptr ⟨192⟩ + UInt256.ofNat (32 * i))
        (marketReadMemory mem ptr id out) = calldataWord out (32 * i)) ∧
      MemoryPrefix mem (marketReadMemory mem ptr id out) ptr.toNat ∧
      RD (deployedRuntime v) I g s0 ret (nextCursor ptr ⟨192⟩ :: R)
        (marketReadMemory mem ptr id out) aw' out σ k' C') := by
  have hbound : ptr.toNat + 384 < 2 ^ 64 :=
    (allocationFits_aligned ptr ⟨384⟩ (by decide +kernel)).mp hfit
  have hdst : (nextCursor ptr ⟨192⟩).toNat = ptr.toNat + 192 :=
    uadd_word_ofNat_toNat ptr 192 (by change _ < 2 ^ 256; omega)
  have hcursor : (nextCursor ptr ⟨384⟩).toNat = ptr.toNat + 384 :=
    uadd_word_ofNat_toNat ptr 384 (lt_trans hbound (by decide))
  have hinput : ptr.toNat ≤ (marketCallMem mem ptr.toNat id).size := by
    rw [marketCallMem_size]; omega
  have hcopied := marketOutputMem_size hinput hlong hout
  have hspan : ptr.toNat + 192 ≤
      (marketOutputMem (marketCallMem mem ptr.toNat id) ptr out).size := by
    rw [hcopied]; omega
  have hptrBound : ptr.toNat + 192 < UInt256.size := by change _ < 2 ^ 256; omega
  have hread (off : Nat) (hoff : off + 32 ≤ 192) := marketReservedMem_load hlo
    hspan hptrBound hoff (marketOutputMem_load hinput hlong hout hptrBound hoff)
  rcases marketDecodeFields v hstack hlong
      (by rw [marketReservedMem_size]; omega) (by rw [hdst])
      (by rw [hdst]; change _ < 2 ^ 256; omega) hread hret rd with
    hbad | ⟨hc, aw', k', C', hdone⟩
  · exact .inl hbad
  · refine .inr ⟨hc, aw', k', C', ?_, ?_, ?_,
      marketReadMemory_prefix mem ptr id out hfit hlong hout, hdone⟩
    · rw [marketReadMemory, marketCopyMem_free
        (by rw [marketReservedMem_size]; omega) (by rw [hdst]; omega),
        marketReservedMem_free, nextCursor_192_twice]
    · rw [hcursor, marketReadMemory, marketCopyMem_size, hdst]; omega
    · intro i hi
      have he : nextCursor ptr ⟨192⟩ + UInt256.ofNat (32 * i) =
          UInt256.ofNat ((nextCursor ptr ⟨192⟩).toNat + 32 * i) := by
        apply u256_inj
        rw [uadd_word_ofNat_toNat _ _ (by rw [hdst]; change _ < 2 ^ 256; omega),
          UInt256.toNat_ofNat_of_lt (by rw [hdst]; change _ < 2 ^ 256; omega)]
      rw [he]
      exact marketCopyMem_field _ _ out i hi
        (by rw [hdst]; change _ < 2 ^ 256; omega)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
