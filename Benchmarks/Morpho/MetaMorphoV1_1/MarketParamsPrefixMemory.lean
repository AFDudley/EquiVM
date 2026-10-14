import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsReturnMemory
import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayInitMemory

/-! Memory preservation through the market-parameter reader's allocation and decode. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem marketParamsInitialMem_prefix (mem : ByteArray) (ptr : UInt256) :
    MemoryPrefix mem (marketParamsInitialMem mem ptr) ptr.toNat := by
  apply (memoryPrefix_sparse_writeWord mem 64 ptr.toNat _ (.inr (by decide))).trans
  apply memoryPrefix_sparse_cascade
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl <;> exact .inl (by omega)

theorem marketParamsCallMem_prefix (mem : ByteArray) (ptr : Nat) (id : UInt256) :
    MemoryPrefix mem (marketParamsCallMem mem ptr id) ptr := by
  apply memoryPrefix_sparse_cascade
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> exact .inl (by omega)

theorem marketParamsOutputMem_prefix {mem out : ByteArray} {ptr : UInt256}
    (hin : ptr.toNat ≤ mem.size) (hl : 160 ≤ out.size) (hh : out.size < UInt256.size) :
    MemoryPrefix mem (marketParamsOutputMem mem ptr out) ptr.toNat := by
  rw [marketParamsOutputMem_long _ _ _ hl hh]
  refine ⟨?_, fun off _ hhi _ ↦ ?_⟩
  · rw [copyWindow_size out mem 0 ptr.toNat 160 (by decide) hl hin]
    exact Nat.le_max_left _ _
  · exact write_read_below_gen_extend out mem ptr.toNat 160 off (by decide) hl hin hhi

theorem marketParamsReservedMem_prefix (mem : ByteArray) (ptr : UInt256) (limit : Nat) :
    MemoryPrefix mem (marketParamsReservedMem mem ptr) limit :=
  (memoryPrefix_sparse_writeWord mem 64 limit _ (.inr (by decide))).trans
    (memoryPrefix_sparse_writeWord _ 64 limit _ (.inr (by decide)))

theorem marketParamsCopyMem_prefix (mem : ByteArray) (dst : Nat) (out : ByteArray) :
    MemoryPrefix mem (marketParamsCopyMem mem dst out) dst :=
  wordSequenceMemory_prefix _ _ _

theorem marketParamsInitialMem_zero {mem : ByteArray} (ptr : UInt256)
    (hmem : mem.size = 96) (hlo : 128 ≤ ptr.toNat) :
    memLoad ⟨96⟩ (marketParamsInitialMem mem ptr) = ⟨0⟩ := by
  let first := writeWord (writeWord mem 64 (nextCursor ptr ⟨160⟩)) ptr.toNat ⟨0⟩
  have hsize : 128 ≤ first.size := by
    simp only [first, writeWord_sparse_size]
    omega
  have hz : memLoad ⟨96⟩ first = ⟨0⟩ := by
    apply mloadWordValue_of_readWithPadding (by change 96 < first.size; omega)
    exact writeWord_read_zero_gap _ ptr.toNat 96 _
      (by rw [writeWord_sparse_size, hmem]; decide) hlo
  have hp : MemoryPrefix first (marketParamsInitialMem mem ptr) ptr.toNat := by
    simp only [marketParamsInitialMem, zeroStruct160Mem, writeCascade_cons, writeCascade_nil]
    exact (memoryPrefix_sparse_writeWord first (ptr.toNat + 32) ptr.toNat ⟨0⟩ (.inl (by omega))).trans
      ((memoryPrefix_sparse_writeWord _ (ptr.toNat + 64) ptr.toNat ⟨0⟩ (.inl (by omega))).trans
        ((memoryPrefix_sparse_writeWord _ (ptr.toNat + 96) ptr.toNat ⟨0⟩ (.inl (by omega))).trans
          (memoryPrefix_sparse_writeWord _ (ptr.toNat + 128) ptr.toNat ⟨0⟩ (.inl (by omega)))))
  exact (hp.load_preserved (by decide) hlo hsize (by decide)).trans hz

theorem marketParamsInitialMem_size (mem : ByteArray) (ptr : UInt256) :
    (marketParamsInitialMem mem ptr).size = max (max mem.size 96) (ptr.toNat + 160) := by
  rw [marketParamsInitialMem, zeroStruct160Mem_size, writeWord_sparse_size]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
