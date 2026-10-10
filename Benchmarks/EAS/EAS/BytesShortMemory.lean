import Benchmarks.EAS.EAS.BytesShortWord
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: a short memory payload becomes the exact packed Solidity storage word.
theorem bytesShortMemoryWord {mem : ByteArray} {ptr : UInt256} {bytes : ByteArray}
    (hl : bytes.size < 32) (hb : ptr.toNat+64 < UInt256.size)
    (hin : bytes.size ≠ 0 → ptr.toNat+64 ≤ mem.size)
    (hread : mem.readWithPadding (ptr.toNat+32) bytes.size = bytes) :
    bytesShortEVMWord (if UInt256.ofNat bytes.size = ⟨0⟩ then ⟨0⟩ else memLoad (ptr+UInt256.ofNat 32) mem)
      (UInt256.ofNat bytes.size) = solidityShortBytesWord bytes := by
  have hsz : (UInt256.ofNat bytes.size).toNat = bytes.size := ulit_toNat' _ (by change bytes.size < 2^256; omega)
  rw [bytesShortEVMWord_eq _ _ (by rw [hsz]; exact hl),hsz]
  have hp : (if UInt256.ofNat bytes.size = ⟨0⟩ then ⟨0⟩ else memLoad (ptr+UInt256.ofNat 32) mem).toByteArray.extract 0 bytes.size = bytes := by
    by_cases hz : bytes.size = 0
    · have he := byteArray_eq_empty_of_size_eq_zero bytes hz
      rw [hz,byteArray_extract_empty_of_le _ (le_refl _)]
      exact he.symm
    · have hw : UInt256.ofNat bytes.size ≠ (⟨0⟩ : UInt256) := by
        intro he
        have h := congrArg UInt256.toNat he
        rw [hsz] at h
        exact hz h
      rw [if_neg hw]
      have hptr : ptr+UInt256.ofNat 32 = UInt256.ofNat (ptr.toNat+32) := by
        apply u256_inj
        rw [uadd_word_ofNat_toNat _ _ (by omega),ulit_toNat' _ (by omega)]
      rw [hptr,memLoad_bytes mem (ptr.toNat+32) (by omega) (by have h := hin hz; omega),
        readWithPadding_prefix mem (ptr.toNat+32) 32 bytes.size (by omega) (by have h := hin hz; omega),hread]
  rw [hp]
  rfl

end Benchmarks.EAS.EAS
