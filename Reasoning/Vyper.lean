import Reasoning.MemCascade
import Reasoning.Storage
import Reasoning.SolmBody
import Solm.VyperStorage

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

/-- Read a scalar leaf through the Vyper backend after validating its reference path. -/
theorem evalExpr_storage_vyper_scalar {cfg : Config} {layout : StorageLayout}
    {bounds : VyperBounds} {solm : Frame} {evm : EVM.State} {slot : StorageRef}
    {er : EvaledStorageRef} {t : ABI.ElemType} {loc : StorageLoc}
    (hbase : solm.locals.get? slot.base = none)
    (her : evalStorageRef cfg solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.storage er = some (.elem t))
    (hbackend : cfg.storageBackend = vyperStorageBackend layout bounds)
    (hcheck : vyperCheckRef? layout bounds evm er = .ok ())
    (hloc : layout er = some (.leaf loc)) :
    evalExpr? cfg solm evm (.storage slot) = .ok (storageLocLoad evm loc) := by
  apply evalExpr_storage_scalar_of_read hbase her hty
  rw [hbackend]
  simp [vyperStorageBackend, hcheck, vyperReadRaw?, vyperLeafLoc?, hloc,
    EvalResult.bind, EvalResult.ofOption, bind, pure]

/-- Write an integer scalar through the Vyper backend. -/
theorem assignStorageRef_storage_vyper_scalar {cfg : Config} {layout : StorageLayout}
    {bounds : VyperBounds} {solm : Frame} {evm evm' : EVM.State}
    {slot : StorageRef} {er : EvaledStorageRef} {ty : StorageType}
    {loc : StorageLoc} {n : Int}
    (hbase : solm.locals.get? slot.base = none)
    (her : evalStorageRef cfg solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.storage er = some ty)
    (hbackend : cfg.storageBackend = vyperStorageBackend layout bounds)
    (hcheck : vyperCheckRef? layout bounds evm er = .ok ())
    (hloc : layout er = some (.leaf loc))
    (hleaf : (∃ t, ty = .elem t) ∨ (∃ name, ty = .contract name))
    (hstore : storageLocStore evm loc (.int n) = some evm') :
    assignStorageRef? cfg solm evm .storage slot (.int n) = .ok (solm, evm') := by
  apply assignStorageRef_storage_of_write hbase her hty
  rw [hbackend]
  rcases hleaf with ⟨t, rfl⟩ | ⟨name, rfl⟩
  · simp [vyperStorageBackend, hcheck, vyperWriteRaw?, vyperLeafLoc?, hloc,
      hstore, EvalResult.bind, EvalResult.ofOption, bind]
  · simp [vyperStorageBackend, hcheck, vyperWriteRaw?, vyperLeafLoc?, hloc,
      hstore, EvalResult.bind, EvalResult.ofOption, bind]

/-- Full-word uint256 read through the Vyper backend. -/
theorem evalExpr_storage_vyper_uint256_backend {cfg : Config} {layout : StorageLayout}
    {bounds : VyperBounds} {solm : Frame} {evm : EVM.State} {slot : StorageRef}
    {er : EvaledStorageRef} {physicalSlot : UInt256}
    (hbase : solm.locals.get? slot.base = none)
    (her : evalStorageRef cfg solm evm slot = .ok er)
    (hty : storageTypeAt? solm.contract.storage er =
      some (.elem (.int (.uint ⟨256, by decide⟩))))
    (hbackend : cfg.storageBackend = vyperStorageBackend layout bounds)
    (hcheck : vyperCheckRef? layout bounds evm er = .ok ())
    (hloc : layout er = some (.leaf (vyperUint256Loc physicalSlot))) :
    evalExpr? cfg solm evm (.storage slot) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner physicalSlot).toNat)) := by
  have hread := evalExpr_storage_vyper_scalar hbase her hty hbackend hcheck hloc
  have hlocEq : vyperUint256Loc physicalSlot = uint256Loc physicalSlot := rfl
  rw [hlocEq, storageLocLoad_uint256] at hread
  exact hread

end Reasoning.Theory
