import Benchmarks.Safe.V3_77901a5.MemoryBytesDecoded
import Benchmarks.Safe.V3_77901a5.WordWrites

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe.V3_77901a5

-- The selector-prefixed ABI buffer has four bytes after its last complete word.
-- The last load can overlap the destination; its padding is discarded by cleanup.
def rawBytesCopyPrefix (mem : ByteArray) (src dst n : Nat) : ByteArray :=
  writeWords mem dst (memoryWords mem (src + 32) n)

def rawBytesCopyLast (mem : ByteArray) (src dst n : Nat) : UInt256 :=
  uInt256OfByteArray ((rawBytesCopyPrefix mem src dst n).readWithPadding
    (src + 32 + 32 * n) 32)

def rawBytesCopyMemory (mem : ByteArray) (src dst n : Nat) : ByteArray :=
  writeWord (writeWord (rawBytesCopyPrefix mem src dst n) (dst + 32 * n)
    (rawBytesCopyLast mem src dst n)) (dst + 32 * n + 4) ⟨0⟩

theorem rawBytesCopyPrefix_size (mem : ByteArray) (src dst n : Nat) (hd : dst ≤ mem.size) :
    (rawBytesCopyPrefix mem src dst n).size = max mem.size (dst + 32 * n) := by
  rw [rawBytesCopyPrefix, writeWords_size _ _ _ hd, memoryWords_length]

theorem rawBytesCopyMemory_size (mem : ByteArray) (src dst n : Nat) (hd : dst ≤ mem.size) :
    (rawBytesCopyMemory mem src dst n).size = max mem.size (dst + 32 * n + 36) := by
  rw [rawBytesCopyMemory, writeWord_sparse_size, writeWord_sparse_size,
    rawBytesCopyPrefix_size _ _ _ _ hd]
  omega

theorem rawBytesCopyMemory_preserved (mem : ByteArray) (src dst n off count : Nat)
    (hd : dst ≤ mem.size) (hin : off + count ≤ mem.size) (ha : off + count ≤ dst) :
    (rawBytesCopyMemory mem src dst n).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [rawBytesCopyMemory, writeWordReadBelow _ _ _ _ _ (by
      rw [writeWord_sparse_size, rawBytesCopyPrefix_size _ _ _ _ hd]; omega) (by omega),
    writeWordReadBelow _ _ _ _ _ (by rw [rawBytesCopyPrefix_size _ _ _ _ hd]; omega)
      (by omega), rawBytesCopyPrefix, writeWords_readBelow _ _ _ _ _ hin ha]

theorem rawBytesCopyMemory_read (mem : ByteArray) (src dst n : Nat)
    (hd : dst ≤ mem.size) (hn : 0 < n)
    (hin : src + 32 + 32 * n + 4 ≤ mem.size)
    (ha : src + 32 + 32 * n + 4 ≤ dst) :
    (rawBytesCopyMemory mem src dst n).readWithPadding dst (32 * n + 4) =
      mem.readWithPadding (src + 32) (32 * n + 4) := by
  have hsize := rawBytesCopyPrefix_size mem src dst n hd
  have hlast : (rawBytesCopyLast mem src dst n).toByteArray.extract 0 4 =
      mem.readWithPadding (src + 32 + 32 * n) 4 := by
    rw [rawBytesCopyLast, toByteArray_uInt256OfByteArray_of_size32 (paddedReadSize _ _ _),
      paddedReadPrefix _ _ _ _ (by omega) (by decide), rawBytesCopyPrefix,
      writeWords_readBelow _ _ _ _ _ hin ha]
  rw [rawBytesCopyMemory, writeWordReadBelow _ _ _ _ _ (by
    rw [writeWord_sparse_size]; omega) (by omega)]
  rw [byteArray_readWithPadding_split_unbounded _ _ _ _ (by omega) (by decide)
    (by rw [writeWord_sparse_size]; omega)]
  rw [writeWordReadBelow _ _ _ _ _ (by omega) (by omega)]
  have htail := writeWord_sparse_read_window (rawBytesCopyPrefix mem src dst n)
    (dst + 32 * n) 0 4 (rawBytesCopyLast mem src dst n)
      (by decide) (by decide) (by decide)
  simp only [Nat.add_zero, Nat.zero_add] at htail
  rw [htail, hlast]
  have hprefix := (memoryWords_view mem (src + 32) n).read
    mem (src + 32) (memoryWords mem (src + 32) n)
      (by rw [memoryWords_length]; omega)
  rw [memoryWords_length] at hprefix
  have hwrite := writeWords_read mem dst (memoryWords mem (src + 32) n)
  rw [memoryWords_length] at hwrite
  rw [rawBytesCopyPrefix, hwrite, ← hprefix]
  exact (byteArray_readWithPadding_split_unbounded mem (src + 32) (32 * n) 4
    (by omega) (by decide) (by omega)).symm

end Benchmarks.Safe.V3_77901a5
