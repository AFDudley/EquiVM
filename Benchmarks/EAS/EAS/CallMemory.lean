import Benchmarks.EAS.EAS.StructEncodeViews
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: truncate a preserved sequence of initialized memory words.
theorem memoryPrefix_read_prefix {before after : ByteArray} {limit : Nat}
    (hp : MemoryPrefix before after limit) (off words len : Nat) (hlo : 96 ≤ off)
    (hhi : off+32*words ≤ limit) (hin : off+32*words ≤ before.size)
    (hb : off+32*words < UInt256.size) (hlen : len ≤ 32*words) :
    after.readWithPadding off len = before.readWithPadding off len := by
  rw [← readWithPadding_prefix after off (32*words) len hlen (le_trans hin hp.size),
    memoryPrefix_read_words hp off words hlo hhi hin hb,
    readWithPadding_prefix before off (32*words) len hlen hin]

-- LIBRARY CANDIDATE: the overlapping selector and first-argument writes of an ABI call.
def selectorArgumentMemory (mem : ByteArray) (off : Nat) (selector argument : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem off selector) (off+4) argument

theorem selectorArgumentMemory_prefix (mem : ByteArray) (off : Nat) (selector argument : UInt256) :
    MemoryPrefix mem (selectorArgumentMemory mem off selector argument) off :=
  (memoryPrefix_sparse_writeWord mem off off selector (Or.inl (le_refl _))).trans
    (memoryPrefix_sparse_writeWord _ (off+4) off argument (Or.inl (by omega)))

theorem selectorArgumentMemory_size (mem : ByteArray) (off : Nat) (selector argument : UInt256) :
    (selectorArgumentMemory mem off selector argument).size = max mem.size (off+36) := by
  simp only [selectorArgumentMemory, writeWord_sparse_size]
  omega

theorem selectorArgumentMemory_selector (mem : ByteArray) (off : Nat) (selector argument : UInt256) :
    (selectorArgumentMemory mem off selector argument).readWithPadding off 4 = selector.toByteArray.extract 0 4 := by
  rw [selectorArgumentMemory, writeWord_read_below_len _ (off+4) off 4 argument (le_refl _)
    (by rw [writeWord_sparse_size]; omega)]
  simpa only [Nat.add_zero, Nat.zero_add] using writeWord_sparse_read_window mem off 0 4 selector
    (by decide) (by decide) (by decide)

theorem selectorArgumentMemory_argument (mem : ByteArray) (off : Nat) (selector argument : UInt256) :
    (selectorArgumentMemory mem off selector argument).readWithPadding (off+4) 32 = argument.toByteArray :=
  writeWord_sparse_read_back _ _ _

theorem selectorArgumentMemory_read (mem : ByteArray) (off : Nat) (selector argument : UInt256) :
    (selectorArgumentMemory mem off selector argument).readWithPadding off 36 =
      selector.toByteArray.extract 0 4 ++ argument.toByteArray := by
  rw [show 36 = 4+32 from rfl, byteArray_readWithPadding_split_unbounded _ off 4 32 (by decide) (by decide)
    (by rw [selectorArgumentMemory_size]; omega),
    selectorArgumentMemory_selector, selectorArgumentMemory_argument]

theorem selectorArgumentMemory_read_of_prefix {mem after : ByteArray} {off limit : Nat} {selector argument : UInt256}
    (hp : MemoryPrefix (selectorArgumentMemory mem off selector argument) after limit)
    (hlo : 96 ≤ off) (hhi : off+36 ≤ limit) (hb : off+36 < UInt256.size) :
    after.readWithPadding off 36 = selector.toByteArray.extract 0 4 ++ argument.toByteArray := by
  have hin : off+36 ≤ (selectorArgumentMemory mem off selector argument).size := by
    rw [selectorArgumentMemory_size]; exact Nat.le_max_right _ _
  rw [show 36 = 4+32 from rfl, byteArray_readWithPadding_split_unbounded _ off 4 32 (by decide) (by decide)
    (le_trans hin hp.size),
    memoryPrefix_read_prefix hp off 1 4 hlo (by omega) (by omega) (by omega) (by decide),
    hp.read (off+4) (by omega) (by omega) (by omega),
    selectorArgumentMemory_selector, selectorArgumentMemory_argument]

end Benchmarks.EAS.EAS
