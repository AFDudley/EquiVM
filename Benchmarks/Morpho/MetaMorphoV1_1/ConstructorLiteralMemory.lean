import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDecodedBuffers

/-! The three empty literal buffers and the version-buffer reservation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

-- LIBRARY CANDIDATE: the natural cursor for an already-aligned allocation.
theorem alignedAllocationCursor (ptr size : Nat) (halign : size % 32 = 0)
    (hsize : size + 31 < UInt256.size) :
    nextCursor (UInt256.ofNat ptr) (UInt256.ofNat size) = UInt256.ofNat (ptr + size) := by
  rw [nextCursor, roundedSize_aligned halign hsize, ofNat_add_words]

-- GENERALIZES allocationFits_aligned to aligned natural sizes and a natural cursor.
theorem alignedAllocationFitsNat (ptr size : Nat) (hptr : ptr < UInt256.size)
    (halign : size % 32 = 0) (hsize : size + 31 < UInt256.size) :
    allocationFits (UInt256.ofNat ptr) (UInt256.ofNat size) ↔ ptr + size < 2 ^ 64 := by
  rw [allocationFits_iff_sum_lt, roundedSize_aligned halign hsize,
    UInt256.toNat_ofNat_of_lt hptr, UInt256.toNat_ofNat_of_lt (by omega)]

def emptyLiteralMemory (mem : ByteArray) (ptr : Nat) : ByteArray :=
  writeWord (writeWord mem 64 (UInt256.ofNat (ptr + 32))) ptr ⟨0⟩

theorem emptyLiteralMemory_free (mem : ByteArray) (ptr : Nat) (hlo : 96 ≤ ptr) :
    memLoad ⟨64⟩ (emptyLiteralMemory mem ptr) = UInt256.ofNat (ptr + 32) := by
  apply loadedWord_of_read
  · change 64 + 32 ≤ _
    simp only [emptyLiteralMemory, writeWord_sparse_size]; omega
  · change (emptyLiteralMemory mem ptr).readWithPadding 64 32 = _
    rw [emptyLiteralMemory, writeWord_sparse_read_preserved _ _ _ _
      (.inl ⟨hlo, by rw [writeWord_sparse_size]; omega⟩), writeWord_sparse_read_back]

theorem emptyLiteralMemory_prefix (mem : ByteArray) (ptr : Nat) :
    ByteMemoryPrefix mem (emptyLiteralMemory mem ptr) ptr :=
  (byteMemoryPrefix_writeWord mem 64 ptr _ (.inr (by decide))).trans
    (byteMemoryPrefix_writeWord _ ptr ptr ⟨0⟩ (.inl (le_refl _)))

def constructorLiteralMemory (mem : ByteArray) (ptr : Nat) : ByteArray :=
  writeWord
    (emptyLiteralMemory (emptyLiteralMemory (emptyLiteralMemory mem ptr) (ptr + 32)) (ptr + 64))
    64 (UInt256.ofNat (ptr + 160))

theorem constructorLiteralMemory_prefix (mem : ByteArray) (ptr : Nat) :
    ByteMemoryPrefix mem (constructorLiteralMemory mem ptr) ptr :=
  (emptyLiteralMemory_prefix mem ptr).trans
    (((emptyLiteralMemory_prefix _ (ptr + 32)).mono (by omega)).trans
      (((emptyLiteralMemory_prefix _ (ptr + 64)).mono (by omega)).trans
        (byteMemoryPrefix_writeWord _ 64 ptr _ (.inr (by decide)))))

theorem constructorLiteralMemory_free (mem : ByteArray) (ptr : Nat) :
    memLoad ⟨64⟩ (constructorLiteralMemory mem ptr) = UInt256.ofNat (ptr + 160) :=
  memLoad_write_same _ 64 ⟨64⟩ _ rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
