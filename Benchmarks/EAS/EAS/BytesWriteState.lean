import Benchmarks.EAS.EAS.StoredBytesWrite
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: preserve the source/EVM state relation through ordered bytes storage loops.
theorem sourceState_clearBytes {s0 ee σ evm} (hs : SourceState s0 ee σ evm)
    (slot : UInt256) (idx fuel : Nat) :
    SourceState s0 ee
      (clearDataWordsForwardFrom ee.codeOwner σ (solidityBytesDataBaseSlot slot) (UInt256.ofNat idx) fuel)
      (clearSolidityBytesDataWordsFrom evm slot idx fuel) := by
  induction fuel generalizing idx σ evm with
  | zero => exact hs
  | succ fuel ih =>
    simp only [clearDataWordsForwardFrom,clearSolidityBytesDataWordsFrom,u256_one_add_ofNat]
    apply ih
    simpa only [solidityBytesDataSlot,hs.env] using hs.storageWrite (solidityBytesDataSlot slot idx) ⟨0⟩

theorem sourceState_writeBytes {s0 ee σ evm} (hs : SourceState s0 ee σ evm)
    (slot : UInt256) (bytes : ByteArray) (idx fuel : Nat) :
    SourceState s0 ee (solidityDataWordsForwardFrom ee.codeOwner σ slot bytes idx fuel)
      (writeSolidityBytesDataWordsFrom evm slot bytes idx fuel) := by
  induction fuel generalizing idx σ evm with
  | zero => exact hs
  | succ fuel ih =>
    simp only [solidityDataWordsForwardFrom,writeSolidityBytesDataWordsFrom]
    apply ih
    simpa only [hs.env] using hs.storageWrite (solidityBytesDataSlot slot idx)
      (uInt256OfByteArray (bytes.readWithPadding (idx*32) 32))

theorem sourceState_bytesClean {s0 ee σ evm} (hs : SourceState s0 ee σ evm)
    (slot : UInt256) (oldLen newLen : Nat) :
    SourceState s0 ee (bytesCleanAccounts σ ee slot oldLen newLen) (bytesWriteClean evm slot oldLen newLen) := by
  unfold bytesCleanAccounts bytesWriteClean
  split
  · exact hs
  · exact sourceState_clearBytes hs slot _ _

theorem sourceState_bytesWrite {s0 ee σ evm} (hs : SourceState s0 ee σ evm)
    (slot : UInt256) (bytes : ByteArray) (oldLen : Nat) :
    SourceState s0 ee (bytesWriteAccounts σ ee slot bytes oldLen) (bytesWriteState evm slot bytes oldLen) := by
  have hc := sourceState_bytesClean hs slot oldLen bytes.size
  dsimp only [bytesWriteAccounts,bytesWriteState]
  split
  · simpa only [hc.env] using hc.storageWrite slot (solidityShortBytesWord bytes)
  · have hw := sourceState_writeBytes hc slot bytes 0 (solidityBytesDataWordCount bytes.size)
    simpa only [hw.env] using hw.storageWrite slot (solidityBytesHeaderWord bytes.size)

end Benchmarks.EAS.EAS
