import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateRowAllocation
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateRowMemory
import Benchmarks.Morpho.MetaMorphoV1_1.BorrowRateSetup

/-! Heap facts after reserving and decoding one reallocation row. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def reallocateRowFinalMem (mem : ByteArray) (ptr : UInt256) (row : ByteArray) : ByteArray :=
  reallocateRowMemory (reallocateRowReservedMem mem ptr) ptr (nextCursor ptr ⟨64⟩) row

theorem reallocateRowReservationBounds {ptr : UInt256} (hf : allocationFits ptr ⟨224⟩) :
    (nextCursor ptr ⟨64⟩).toNat = ptr.toNat + 64 ∧
    (nextCursor ptr ⟨224⟩).toNat = ptr.toNat + 224 ∧ ptr.toNat + 224 < 2 ^ 64 := by
  have hb : ptr.toNat + 224 < 2 ^ 64 := (allocationFits_aligned _ _ (by decide +kernel)).mp hf
  refine ⟨?_, ?_, hb⟩
  · exact uadd_word_ofNat_toNat ptr 64 (lt_of_lt_of_le (by omega : ptr.toNat + 64 < 2 ^ 64) (by decide))
  · exact uadd_word_ofNat_toNat ptr 224 (lt_trans hb (by decide))

theorem reallocateRowFinalMem_prefix (mem row : ByteArray) (ptr : UInt256)
    (hf : allocationFits ptr ⟨224⟩) : MemoryPrefix mem (reallocateRowFinalMem mem ptr row) ptr.toNat := by
  have hb := (reallocateRowReservationBounds hf).1
  exact ((memoryPrefix_sparse_writeWord mem 64 ptr.toNat _ (.inr (by decide))).trans
    (memoryPrefix_sparse_writeWord _ 64 ptr.toNat _ (.inr (by decide)))).trans
    ((reallocateRowStructMem_prefix _ row ptr (nextCursor ptr ⟨64⟩) (by omega)).trans
      (twoWordHashMem_prefix _ _ _ _))

theorem reallocateRowFinalMem_size {mem row : ByteArray} {ptr : UInt256}
    (hlo : 96 ≤ ptr.toNat) (hf : allocationFits ptr ⟨224⟩) :
    (reallocateRowFinalMem mem ptr row).size = max mem.size (ptr.toNat + 224) := by
  have hb := (reallocateRowReservationBounds hf).1
  have hs : (reallocateRowStructMem (reallocateRowReservedMem mem ptr) ptr
      (nextCursor ptr ⟨64⟩) row).size = max mem.size (ptr.toNat + 224) := by
    rw [reallocateRowStructMem_size _ _ _ _ (by omega)]
    simp only [reallocateRowReservedMem, writeWord_sparse_size, hb]
    omega
  rw [reallocateRowFinalMem, reallocateRowMemory,
    twoWordHashMem_size_of_ge_64' _ _ (by rw [hs]; omega), hs]

theorem reallocateRowFinalMem_free {mem row : ByteArray} {ptr : UInt256}
    (hlo : 96 ≤ ptr.toNat) (hf : allocationFits ptr ⟨224⟩) :
    memLoad ⟨64⟩ (reallocateRowFinalMem mem ptr row) = nextCursor ptr ⟨224⟩ := by
  have hb := (reallocateRowReservationBounds hf).1
  rw [reallocateRowFinalMem, reallocateRowMemory,
    twoWordHashMem_free _ _ (by rw [reallocateRowStructMem_size _ _ _ _ (by omega)]; omega),
    reallocateRowStructMem_free (by simp only [reallocateRowReservedMem, writeWord_sparse_size]; omega)
      hlo (by omega)]
  exact memLoad_write_same _ _ _ _ rfl

theorem reallocateRowFinalMem_params {mem row : ByteArray} {ptr : UInt256}
    (hlo : 96 ≤ ptr.toNat) (hf : allocationFits ptr ⟨224⟩) :
    memLoad ptr (reallocateRowFinalMem mem ptr row) = nextCursor ptr ⟨64⟩ := by
  have hb := (reallocateRowReservationBounds hf).1
  have hp := (twoWordHashMem_prefix
    (reallocateRowStructMem (reallocateRowReservedMem mem ptr) ptr (nextCursor ptr ⟨64⟩) row)
    (marketParamsData row).id ⟨13⟩ (ptr.toNat + 32)).load_preserved hlo (le_refl _)
      (by rw [reallocateRowStructMem_size _ _ _ _ (by omega)]; omega) ptr.val.isLt
  rw [u256_ofNat_toNat] at hp
  exact hp.trans (reallocateRowStructMem_params (by omega))

theorem reallocateRowFinalMem_assets {mem row : ByteArray} {ptr : UInt256}
    (hlo : 96 ≤ ptr.toNat) (hf : allocationFits ptr ⟨224⟩) :
    memLoad (ptr + ⟨32⟩) (reallocateRowFinalMem mem ptr row) = calldataWord row 160 := by
  obtain ⟨hb, _, hhi⟩ := reallocateRowReservationBounds hf
  have hm : ptr.toNat + 224 < UInt256.size := lt_trans hhi (by decide)
  have ha : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 := uadd_word_ofNat_toNat ptr 32 (by omega)
  have hp := (twoWordHashMem_prefix
    (reallocateRowStructMem (reallocateRowReservedMem mem ptr) ptr (nextCursor ptr ⟨64⟩) row)
    (marketParamsData row).id ⟨13⟩ (ptr.toNat + 64)).load_preserved
      (off := (ptr + ⟨32⟩).toNat) (by omega) (by omega)
      (by rw [reallocateRowStructMem_size _ _ _ _ (by omega)]; omega) (by rw [ha]; omega)
  rw [u256_ofNat_toNat] at hp
  exact hp.trans (reallocateRowStructMem_assets (by omega))

theorem reallocateRowFinalMem_loads {mem row : ByteArray} {ptr : UInt256}
    (hlo : 96 ≤ ptr.toNat) (hf : allocationFits ptr ⟨224⟩) (hc : MarketParamsChecks row) :
    MarketParamsLoads (reallocateRowFinalMem mem ptr row) (nextCursor ptr ⟨64⟩) (marketParamsData row) := by
  obtain ⟨hb, _, hhi⟩ := reallocateRowReservationBounds hf
  have hm : (nextCursor ptr ⟨64⟩).toNat + 160 < UInt256.size := by
    rw [hb]
    exact lt_trans hhi (by decide)
  exact (reallocateRowStructMem_loads hc (by omega) hm).prefix
    (twoWordHashMem_prefix _ _ _ (ptr.toNat + 224)) (by omega)
    (by rw [reallocateRowStructMem_size _ _ _ _ (by omega)]; omega) (by omega) hm

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
