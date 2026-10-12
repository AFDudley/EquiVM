import Reasoning.MemCascade
import Reasoning.Storage
import Reasoning.SolmBody
import Solm.VyperLayout

/-!
# Vyper storage and mapping-hash bridges

Vyper hashes a mapping's base slot before its key. The memory lemmas below connect
the two `MSTORE`s and `KECCAK256` in a Vyper trace to `Solm.vyperMappingSlot`.
Scalar leaves use the configured storage layout and the backend-neutral helpers in
`Reasoning.SolmBody`.
-/

open Ethereum Ethereum.EVM Solm ABI

namespace Reasoning.Theory

/-- The EVM hash of the Vyper preimage `baseSlot ++ key` is the Solm mapping slot. -/
theorem vyperMappingSlot_hash (baseSlot : UInt256) (key : KeyValue) :
    UInt256.ofNat (fromByteArrayBigEndian
      (KEC (baseSlot.toByteArray ++ (keyValueToWord key).toByteArray))) =
      vyperMappingSlot baseSlot key := by
  unfold vyperMappingSlot
  exact keccakSlot_eq _

/-- Address-key version for traces that already hold a canonical address as an EVM word. -/
theorem vyperMappingSlot_hash_address (baseSlot key : UInt256)
    (hcanon : key.toNat < EVM.addressModulus) :
    UInt256.ofNat (fromByteArrayBigEndian
      (KEC (baseSlot.toByteArray ++ key.toByteArray))) =
      vyperMappingSlot baseSlot (.address (AccountAddress.ofNat key.toNat)) := by
  simpa only [keyValueToWord_address_of_canonical key hcanon] using
    vyperMappingSlot_hash baseSlot (.address (AccountAddress.ofNat key.toNat))

/-- A Vyper mapping hash can be proved from the two words stored in scratch memory,
regardless of the initial memory size. -/
theorem twoWordHashMem_vyperMappingSlot (baseSlot : UInt256) (key : KeyValue)
    (mem : ByteArray) :
    UInt256.ofNat (fromByteArrayBigEndian
      (KEC ((twoWordHashMem baseSlot (keyValueToWord key) mem).readWithPadding 0 64))) =
      vyperMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64_any]
  exact vyperMappingSlot_hash baseSlot key

/-- Vyper traces commonly write the key at byte 32 before writing the base slot at byte 0. -/
theorem wordAt0Mem_wordAt32Mem_vyperMappingSlot
    (baseSlot : UInt256) (key : KeyValue) {mem : ByteArray}
    (hmem : 64 ≤ mem.size) :
    UInt256.ofNat (fromByteArrayBigEndian
      (KEC ((wordAt0Mem baseSlot (wordAt32Mem (keyValueToWord key) mem)).readWithPadding 0 64))) =
      vyperMappingSlot baseSlot key := by
  rw [wordAt0Mem_wordAt32Mem_read0_64 baseSlot (keyValueToWord key) hmem]
  exact vyperMappingSlot_hash baseSlot key

/-- Read a full-word Vyper scalar leaf using its layout location. -/
theorem evalExpr_storage_vyper_uint256 {cfg : Config} {layout : StorageLayout}
    {solm : Frame} {evm : EVM.State} {slot : StorageRef}
    {er : EvaledStorageRef} {physicalSlot : UInt256}
    (hbase : solm.locals.get? slot.base = none)
    (her : evalStorageRef cfg solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.storage er =
      some (.elem (.int (.uint ⟨256, by decide⟩))))
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hloc : layout er = some (.leaf (vyperUint256Loc physicalSlot))) :
    evalExpr? cfg solm evm (.storage slot) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner physicalSlot).toNat)) := by
  have hread := evalExpr_storage_scalar hbase her hty hbackend hloc
  have hlocEq : vyperUint256Loc physicalSlot = uint256Loc physicalSlot := rfl
  rw [hlocEq, storageLocLoad_uint256] at hread
  exact hread

/-- Write a full-word Vyper scalar leaf through its configured layout. -/
theorem assignStorageRef_storage_vyper_uint256 {cfg : Config} {layout : StorageLayout}
    {solm : Frame} {evm evm' : EVM.State} {slot : StorageRef}
    {er : EvaledStorageRef} {physicalSlot : UInt256} {value : Value}
    (hbase : solm.locals.get? slot.base = none)
    (her : evalStorageRef cfg solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.storage er =
      some (.elem (.int (.uint ⟨256, by decide⟩))))
    (hbackend : cfg.storageBackend = solidityStorageBackend layout)
    (hloc : layout er = some (.leaf (vyperUint256Loc physicalSlot)))
    (hstore : storageLocStore evm (vyperUint256Loc physicalSlot) value = some evm') :
    assignStorageRef? cfg solm evm .storage slot value = .ok (solm, evm') := by
  apply assignStorageRef_storage_of_write hbase her hty
  rw [hbackend]
  exact solidityStorageBackend_write_elem layout er _ value evm evm'
    (vyperUint256Loc physicalSlot) hloc hstore

end Reasoning.Theory
