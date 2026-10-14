import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateRowFields
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsDecoded
import Benchmarks.Morpho.MetaMorphoV1_1.MarketParamsPrefixMemory
import Benchmarks.Morpho.MetaMorphoV1_1.MappingScratchMemory

/-! The allocated MarketAllocation header and its five-word MarketParams object. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def reallocateRowStructMem (mem : ByteArray) (allocation params : UInt256)
    (row : ByteArray) : ByteArray :=
  writeWord (writeWord (marketParamsCopyMem mem params.toNat row) allocation.toNat params)
    (allocation.toNat + 32) (calldataWord row 160)

theorem reallocateRowStructMem_size (mem row : ByteArray) (allocation params : UInt256)
    (hsep : allocation.toNat + 64 ≤ params.toNat) :
    (reallocateRowStructMem mem allocation params row).size = max mem.size (params.toNat + 160) := by
  simp only [reallocateRowStructMem, writeWord_sparse_size, marketParamsCopyMem_size]
  omega

theorem reallocateRowStructMem_prefix (mem row : ByteArray) (allocation params : UInt256)
    (hsep : allocation.toNat ≤ params.toNat) :
    MemoryPrefix mem (reallocateRowStructMem mem allocation params row) allocation.toNat :=
  ((marketParamsCopyMem_prefix mem params.toNat row).mono hsep).trans
    ((memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _))).trans
      (memoryPrefix_sparse_writeWord _ _ _ _ (.inl (by omega))))

theorem reallocateRowStructMem_free {mem row : ByteArray} {allocation params : UInt256}
    (hmem : 96 ≤ mem.size) (hlo : 96 ≤ allocation.toNat)
    (hsep : allocation.toNat + 64 ≤ params.toNat) :
    memLoad ⟨64⟩ (reallocateRowStructMem mem allocation params row) = memLoad ⟨64⟩ mem := by
  rw [reallocateRowStructMem, memLoad_write_above _ _ _ _
      (by simp only [writeWord_sparse_size, marketParamsCopyMem_size]; change 64 + 32 ≤ _; omega)
      (by change 64 + 32 ≤ allocation.toNat + 32; omega),
    memLoad_write_above _ _ _ _ (by rw [marketParamsCopyMem_size]; change 64 + 32 ≤ _; omega)
      (by change 64 + 32 ≤ allocation.toNat; omega),
    marketParamsCopyMem_free hmem (by omega)]

theorem reallocateRowStructMem_params {mem row : ByteArray} {allocation params : UInt256}
    (hsep : allocation.toNat + 64 ≤ params.toNat) :
    memLoad allocation (reallocateRowStructMem mem allocation params row) = params := by
  rw [reallocateRowStructMem, memLoad_write_above _ _ _ _
    (by simp only [writeWord_sparse_size, marketParamsCopyMem_size]; omega) (by omega)]
  exact memLoad_write_same _ _ _ _ rfl

theorem reallocateRowStructMem_assets {mem row : ByteArray} {allocation params : UInt256}
    (hfit : allocation.toNat + 64 < UInt256.size) :
    memLoad (allocation + UInt256.ofNat 32) (reallocateRowStructMem mem allocation params row) =
      calldataWord row 160 :=
  memLoad_write_same _ _ _ _ (uadd_word_ofNat_toNat allocation 32 (by omega))

theorem reallocateRowStructMem_field {mem row : ByteArray} {allocation params : UInt256}
    (hsep : allocation.toNat + 64 ≤ params.toNat)
    (hfit : params.toNat + 160 < UInt256.size) (i : Nat) (hi : i < 5) :
    memLoad (params + UInt256.ofNat (32 * i))
      (reallocateRowStructMem mem allocation params row) = calldataWord row (32 * i) := by
  have hadd : (params + UInt256.ofNat (32 * i)).toNat = params.toNat + 32 * i :=
    uadd_word_ofNat_toNat params (32 * i) (by omega)
  have houter : memLoad (params + UInt256.ofNat (32 * i))
      (reallocateRowStructMem mem allocation params row) =
      memLoad (params + UInt256.ofNat (32 * i))
        (writeWord (marketParamsCopyMem mem params.toNat row) allocation.toNat params) :=
    memLoad_write_disjoint _ _ _ _
      (by rw [hadd, writeWord_sparse_size, marketParamsCopyMem_size]; omega)
      (.inr (by rw [hadd]; omega))
  have hinner : memLoad (params + UInt256.ofNat (32 * i))
      (writeWord (marketParamsCopyMem mem params.toNat row) allocation.toNat params) =
      memLoad (params + UInt256.ofNat (32 * i)) (marketParamsCopyMem mem params.toNat row) :=
    memLoad_write_disjoint _ _ _ _
      (by rw [hadd, marketParamsCopyMem_size]; omega) (.inr (by rw [hadd]; omega))
  rw [houter, hinner]
  have he : params + UInt256.ofNat (32 * i) = UInt256.ofNat (params.toNat + 32 * i) := by
    apply u256_inj
    rw [hadd, UInt256.toNat_ofNat_of_lt (by omega)]
  rw [he]
  exact marketParamsCopyMem_field mem params.toNat row i hi hfit

theorem reallocateRowStructMem_loads {mem row : ByteArray} {allocation params : UInt256}
    (hc : MarketParamsChecks row) (hsep : allocation.toNat + 64 ≤ params.toNat)
    (hfit : params.toNat + 160 < UInt256.size) :
    MarketParamsLoads (reallocateRowStructMem mem allocation params row) params (marketParamsData row) :=
  marketParamsLoads_of_fields hc (reallocateRowStructMem_field hsep hfit)

theorem reallocateRowStructMem_hash {mem row : ByteArray} {allocation params : UInt256}
    (hc : MarketParamsChecks row) (hsep : allocation.toNat + 64 ≤ params.toNat)
    (hfit : params.toNat + 160 < UInt256.size) :
    keccakWord params ⟨160⟩ (reallocateRowStructMem mem allocation params row) =
      (marketParamsData row).id := by
  have hbytes := marketParamsBytes_of_fields
    (mem := reallocateRowStructMem mem allocation params row) (src := params) hc
    (by rw [reallocateRowStructMem_size _ _ _ _ hsep]; omega) hfit
    (reallocateRowStructMem_field hsep hfit)
  rw [keccakWord, show (⟨160⟩ : UInt256).toNat = 160 from rfl, hbytes,
    MarketParamsData.id, uInt256OfByteArray_eq]

def reallocateRowMemory (mem : ByteArray) (allocation params : UInt256) (row : ByteArray) : ByteArray :=
  twoWordHashMem (marketParamsData row).id ⟨13⟩ (reallocateRowStructMem mem allocation params row)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
