import Benchmarks.Safe.ViaIR.MemoryBytesEncodingInto
import Benchmarks.Safe.ViaIR.MemoryBytesDecoded

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

-- LIBRARY CANDIDATE: the ABI tuple consisting of a static word and dynamic bytes.
def wordBytesArgsMemory (mem : ByteArray) (base len : Nat) (word : UInt256)
    (words : List UInt256) : ByteArray :=
  memoryBytesEncodedInto (writeWords mem base [word, ⟨64⟩]) (base + 64) len words

theorem wordBytesArgsMemory_size (mem : ByteArray) (base len : Nat) (word : UInt256)
    (words : List UInt256) (hn : words.length = (len + 31) / 32) :
    (wordBytesArgsMemory mem base len word words).size = max mem.size (base + 128 + len) := by
  rw [wordBytesArgsMemory, memoryBytesEncodedInto_size _ _ _ _ hn,
    writeWords_size_nonempty _ _ _ (by simp)]
  simp only [List.length_cons, List.length_nil]
  omega

theorem wordBytesArgsMemory_preserved (mem : ByteArray) (base len off count : Nat)
    (word : UInt256) (words : List UInt256)
    (hin : off + count ≤ mem.size) (ha : off + count ≤ base) :
    (wordBytesArgsMemory mem base len word words).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [wordBytesArgsMemory, memoryBytesEncodedInto_preserved _ _ _ _ _ _ (by
    rw [writeWords_size_nonempty _ _ _ (by simp)]; omega) (by omega),
    writeWords_readBelow _ _ _ _ _ hin ha]

theorem wordBytesArgsMemory_read (mem : ByteArray) (base len : Nat) (word : UInt256)
    (words : List UInt256) (hn : words.length = (len + 31) / 32) :
    (wordBytesArgsMemory mem base len word words).readWithPadding base
      (96 + 32 * words.length) =
      wordBytes [word, ⟨64⟩, UInt256.ofNat len] ++ (wordBytes words).extract 0 len ++
        ByteArray.zeroes (32 * words.length - len) := by
  have hh : (wordBytesArgsMemory mem base len word words).readWithPadding base 64 =
      wordBytes [word, ⟨64⟩] := by
    rw [wordBytesArgsMemory, memoryBytesEncodedInto_preserved _ _ _ _ _ _ (by
      rw [writeWords_size_nonempty _ _ _ (by simp)]; simp) (by omega)]
    exact writeWords_read mem base [word, ⟨64⟩]
  have ht : (wordBytesArgsMemory mem base len word words).readWithPadding (base + 64)
      (32 + 32 * words.length) =
      (UInt256.ofNat len).toByteArray ++ (wordBytes words).extract 0 len ++
        ByteArray.zeroes (32 * words.length - len) :=
    memoryBytesEncodedInto_read _ _ _ _ hn
  rw [show 96 + 32 * words.length = 64 + (32 + 32 * words.length) by omega,
    byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by omega)
      (by rw [wordBytesArgsMemory_size _ _ _ _ _ hn, hn]; omega), hh, ht]
  simp only [wordBytes, ByteArray.append_empty, ByteArray.append_assoc]

end Benchmarks.Safe.ViaIR
