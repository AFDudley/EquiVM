import Benchmarks.Morpho.MetaMorphoV1_1.WordCallMemory
import Benchmarks.Morpho.MetaMorphoV1_1.CallReturnMemory

/-! Allocate a length-prefixed selector and arbitrary fixed sequence of ABI words. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

-- GENERALIZES safeTransferRequestMemory to any nonempty sequence of static ABI words.
def encodedWordCallMemory (mem : ByteArray) (ptr selector : UInt256) (words : List UInt256) : ByteArray :=
  writeWord (wordCallMemory mem (ptr.toNat + 32) selector words) ptr.toNat
    (UInt256.ofNat (4 + 32 * words.length))

def allocatedWordCallMemory (mem : ByteArray) (ptr selector : UInt256) (words : List UInt256) : ByteArray :=
  writeWord (encodedWordCallMemory mem ptr selector words) 64
    (nextCursor ptr (UInt256.ofNat (36 + 32 * words.length)))

theorem encodedWordCallMemory_size (mem : ByteArray) (ptr selector : UInt256)
    {words : List UInt256} (hne : words ≠ []) :
    (encodedWordCallMemory mem ptr selector words).size =
      max mem.size (ptr.toNat + 36 + 32 * words.length) := by
  rw [encodedWordCallMemory, writeWord_sparse_size, wordCallMemory_size _ _ _ hne]
  omega

theorem allocatedWordCallMemory_size (mem : ByteArray) (ptr selector : UInt256)
    {words : List UInt256} (hne : words ≠ []) :
    (allocatedWordCallMemory mem ptr selector words).size =
      max (max mem.size (ptr.toNat + 36 + 32 * words.length)) 96 := by
  rw [allocatedWordCallMemory, writeWord_sparse_size, encodedWordCallMemory_size _ _ _ hne]

theorem allocatedWordCallMemory_free (mem : ByteArray) (ptr selector : UInt256) (words : List UInt256) :
    memLoad ⟨64⟩ (allocatedWordCallMemory mem ptr selector words) =
      nextCursor ptr (UInt256.ofNat (36 + 32 * words.length)) := memLoad_write_same _ _ _ _ rfl

theorem allocatedWordCallMemory_length (mem : ByteArray) (ptr selector : UInt256)
    {words : List UInt256} (hne : words ≠ []) (hlo : 96 ≤ ptr.toNat) :
    memLoad ptr (allocatedWordCallMemory mem ptr selector words) =
      UInt256.ofNat (4 + 32 * words.length) := by
  rw [allocatedWordCallMemory, Reasoning.Theory.writeWord, memLoad_write_disjoint _ 64 ptr _
    (by rw [encodedWordCallMemory_size _ _ _ hne]; omega) (.inr hlo)]
  exact memLoad_write_same _ _ _ _ rfl

theorem allocatedWordCallMemory_read (mem : ByteArray) (ptr selector : UInt256)
    {words : List UInt256} (hne : words ≠ []) (hlo : 96 ≤ ptr.toNat) :
    (allocatedWordCallMemory mem ptr selector words).readWithPadding (ptr.toNat + 32)
      (4 + 32 * words.length) = selector.toByteArray.extract 0 4 ++ wordBytes words := by
  rw [allocatedWordCallMemory, writeWord_sparse_read_preserved_unbounded _ _ _ _ _
    (by rw [encodedWordCallMemory_size _ _ _ hne]; omega) (.inr (by omega)),
    encodedWordCallMemory, writeWord_sparse_read_preserved_unbounded _ _ _ _ _
      (by rw [wordCallMemory_size _ _ _ hne]; omega) (.inr (by omega)), wordCallMemory_read]

theorem allocatedWordCallMemory_prefix (mem : ByteArray) (ptr selector : UInt256)
    (words : List UInt256) : MemoryPrefix mem (allocatedWordCallMemory mem ptr selector words) ptr.toNat :=
  ((wordCallMemory_prefix mem (ptr.toNat + 32) selector words).mono (by omega)).trans
    ((memoryPrefix_sparse_writeWord _ _ _ _ (.inl (le_refl _))).trans
      (memoryPrefix_sparse_writeWord _ 64 _ _ (.inr (by decide))))

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
