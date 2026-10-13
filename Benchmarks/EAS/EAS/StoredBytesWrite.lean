import Benchmarks.EAS.EAS.StoredBytes
import Reasoning.ExternalCall
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: a valid Solidity bytes header's packing flag is determined by its length.
theorem storedBytesPacked_iff {evm : EVM.State} {slot : UInt256}
    (hv : storedBytesValid (EVM.storageLoad evm evm.executionEnv.codeOwner slot)) :
    checkBytesPacked slot evm = decide ((storedBytesLengthWord (EVM.storageLoad evm evm.executionEnv.codeOwner slot)).toNat < 32) := by
  let header := EVM.storageLoad evm evm.executionEnv.codeOwner slot
  by_cases hf : UInt256.land header ⟨1⟩ = ⟨0⟩
  · have hl : (storedBytesLengthWord header).toNat < 32 := by
      have hne : UInt256.lt (storedBytesLengthWord header) ⟨32⟩ ≠ ⟨0⟩ := by
        intro hz
        exact hv (hf.trans hz.symm)
      exact ult_ne_zero_toNat_lt hne
    rw [checkBytesPacked_of_storageLoad_land_one_zero rfl hf,decide_eq_true hl]
  · have hl : ¬ (storedBytesLengthWord header).toNat < 32 := by
      intro hlt
      exact hv ((land_one_eq_one_of_ne_zero hf).trans (ult_one hlt).symm)
    rw [checkBytesPacked_of_storageLoad_land_one_ne_zero rfl hf,decide_eq_false hl]

-- LIBRARY CANDIDATE: ordered state and account-map forms of a bytes assignment.
def bytesWriteClean (evm : EVM.State) (slot : UInt256) (oldLen newLen : Nat) : EVM.State :=
  if oldLen < 32 then evm else
    let first := if newLen < 32 then 0 else solidityBytesDataWordCount newLen
    clearSolidityBytesDataWordsFrom evm slot first (solidityBytesDataWordCount oldLen-first)

def bytesWriteState (evm : EVM.State) (slot : UInt256) (bytes : ByteArray) (oldLen : Nat) : EVM.State :=
  let clean := bytesWriteClean evm slot oldLen bytes.size
  if bytes.size < 32 then
    EVM.storageStore clean clean.executionEnv.codeOwner slot (solidityShortBytesWord bytes)
  else
    let data := writeSolidityBytesDataWordsFrom clean slot bytes 0 (solidityBytesDataWordCount bytes.size)
    EVM.storageStore data data.executionEnv.codeOwner slot (solidityBytesHeaderWord bytes.size)

def bytesCleanAccounts (σ : AccountMap) (ee : ExecutionEnv) (slot : UInt256) (oldLen newLen : Nat) : AccountMap :=
  if oldLen < 32 then σ else
    let first := if newLen < 32 then 0 else solidityBytesDataWordCount newLen
    clearDataWordsForwardFrom ee.codeOwner σ (solidityBytesDataBaseSlot slot) (UInt256.ofNat first)
      (solidityBytesDataWordCount oldLen-first)

def bytesWriteAccounts (σ : AccountMap) (ee : ExecutionEnv) (slot : UInt256) (bytes : ByteArray) (oldLen : Nat) : AccountMap :=
  let clean := bytesCleanAccounts σ ee slot oldLen bytes.size
  if bytes.size < 32 then sstoreAccountMap ee.codeOwner clean slot (solidityShortBytesWord bytes)
  else sstoreAccountMap ee.codeOwner
    (solidityDataWordsForwardFrom ee.codeOwner clean slot bytes 0 (solidityBytesDataWordCount bytes.size))
    slot (solidityBytesHeaderWord bytes.size)

theorem storedBytesWrite {cfg : Config} {layout : StorageLayout} {evm : EVM.State}
    {er : EvaledStorageRef} {slot : UInt256} (bytes : ByteArray)
    (hcfg : cfg.storageBackend = solidityStorageBackend layout) (hloc : layout er = some (.anchor slot)) :
    cfg.storageBackend.write er .bytes (.bytes bytes) evm =
      if storedBytesValid (EVM.storageLoad evm evm.executionEnv.codeOwner slot) then
        .ok (bytesWriteState evm slot bytes (storedBytesLengthWord (EVM.storageLoad evm evm.executionEnv.codeOwner slot)).toNat)
      else .revert := by
  simp only [hcfg,solidityStorageBackend,solidityWriteStorage?,solidityWriteBytesValue?,
    solidityBytesBaseSlotAndLength?,solidityAnchor?,hloc,storedBytesDecode]
  by_cases hv : storedBytesValid (EVM.storageLoad evm evm.executionEnv.codeOwner slot)
  · simp only [if_pos hv]
    rw [storedBytesPacked_iff hv]
    by_cases hn : bytes.size < 32 <;>
      by_cases ho : (storedBytesLengthWord (EVM.storageLoad evm evm.executionEnv.codeOwner slot)).toNat < 32 <;>
      simp only [bytesWriteState,bytesWriteClean,hn,ho,if_true,if_false,decide_true,decide_false,
        Nat.sub_zero,solidityStateResultToEval,Bool.false_eq_true]
  · simp only [if_neg hv,solidityStateResultToEval]

end Benchmarks.EAS.EAS
