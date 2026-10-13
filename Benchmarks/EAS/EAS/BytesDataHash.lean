import Benchmarks.EAS.EAS.StoredWords
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: normalize the one-word storage-data hash to its base slot.
theorem bytesDataHash (slot : UInt256) (mem : ByteArray) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 32)
      (slot.toByteArray.write 0 mem (UInt256.ofNat 0).toNat 32) = solidityBytesDataBaseSlot slot := by
  have h := storedBytesDataHash slot mem
  change keccakWord (UInt256.ofNat 0) (UInt256.ofNat 32)
    (Reasoning.Theory.writeWord mem 0 slot) = solidityBytesDataBaseSlot slot + ⟨0⟩ at h
  rw [uint256_add_zero_right] at h
  exact h

end Benchmarks.EAS.EAS
