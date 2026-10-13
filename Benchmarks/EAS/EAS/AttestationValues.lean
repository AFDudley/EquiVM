import Benchmarks.EAS.EAS.CopyStoredFields
import Benchmarks.EAS.EAS.CopyStoredSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- GENERALIZES Reasoning.Storage.storageLocLoad_bool_offset0 to any packed byte.
theorem storageLocLoad_bool_offset (evm : EVM.State) (slot : UInt256) (offset : Fin 32)
    {hbound : offset.val + (1 : Fin 33).val - 1 < 32} :
    storageLocLoad evm {slot := slot, offset := offset, size := 1, hbound := hbound, type := .bool} =
      wordToElem .bool (UInt256.land (UInt256.div (EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        (UInt256.ofNat (256^offset.val))) ⟨255⟩) := by
  unfold storageLocLoad
  apply congrArg (wordToElem .bool)
  apply u256_inj
  change fromBytes' ((EVM.Word.toBytesLEWithSizeProof
    (EVM.storageLoad evm evm.executionEnv.codeOwner slot)).1.extract offset.val (offset.val + 1)) = _
  rw [List.extract_eq_take_drop]
  simpa only [Nat.add_sub_cancel_left] using fromBytes'_drop_take_wordLE_land_div_mask
    (EVM.storageLoad evm evm.executionEnv.codeOwner slot) offset.val 1 (by have := offset.isLt; omega) (by decide)

theorem attestationU64_read (evm : EVM.State) (slot : UInt256) (offset : Fin 32)
    (hbound : offset.val + 8 - 1 < 32) :
    storageLocLoad evm (attestationU64Loc slot offset hbound) =
      .int (Int.ofNat (UInt256.land
        (UInt256.shiftRight (EVM.storageLoad evm evm.executionEnv.codeOwner slot) (UInt256.ofNat (8*offset.val)))
        ⟨18446744073709551615⟩).toNat) := by
  rw [wordShiftRight_div _ _ (by have := offset.isLt; omega)]
  have hp : 256^offset.val = 2^(8*offset.val) := by rw [pow_mul]; rfl
  simpa only [attestationU64Loc, hp] using
    storageLocLoad_uint_offset evm slot offset (8 : Fin 33) (⟨64, by decide⟩ : ABI.BitWidth)
      (hbound := hbound) rfl (by have := offset.isLt; omega) (by decide)

theorem attestationBool_read (evm : EVM.State) (slot : UInt256) :
    storageLocLoad evm (attestationBoolLoc slot) =
      wordToElem .bool (UInt256.land
        (UInt256.shiftRight (EVM.storageLoad evm evm.executionEnv.codeOwner slot) (UInt256.ofNat 160)) ⟨255⟩) := by
  rw [wordShiftRight_div _ _ (by decide)]
  exact storageLocLoad_bool_offset evm slot (20 : Fin 32)

end Benchmarks.EAS.EAS
