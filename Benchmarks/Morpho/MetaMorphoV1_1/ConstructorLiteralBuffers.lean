import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorLiteralMemory

/-! Empty and version literals stored in the constructor's allocated memory. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem emptyLiteralMemory_buffer (mem : ByteArray) (ptr : Nat) (hptr : ptr < UInt256.size) :
    BytesBuffer (emptyLiteralMemory mem ptr) (UInt256.ofNat ptr) ByteArray.empty := by
  refine ⟨?_, ?_, ?_⟩
  · rw [UInt256.toNat_ofNat_of_lt hptr, ByteArray.size_empty, Nat.add_zero,
      emptyLiteralMemory, writeWord_sparse_size]
    omega
  · exact memLoad_write_same _ ptr (UInt256.ofNat ptr) ⟨0⟩ (UInt256.toNat_ofNat_of_lt hptr)
  · rw [ByteArray.size_empty, byteArray_readWithPadding_zero]

theorem constructorLiteralMemory_empty0 (mem : ByteArray) (ptr : Nat)
    (hlo : 96 ≤ ptr) (hptr : ptr < UInt256.size) :
    BytesBuffer (constructorLiteralMemory mem ptr) (UInt256.ofNat ptr) ByteArray.empty := by
  have h0 := emptyLiteralMemory_buffer mem ptr hptr
  have hp : ByteMemoryPrefix (emptyLiteralMemory mem ptr)
      (constructorLiteralMemory mem ptr) (ptr + 32) :=
    (emptyLiteralMemory_prefix (emptyLiteralMemory mem ptr) (ptr + 32)).trans
    (((emptyLiteralMemory_prefix _ (ptr + 64)).mono (by omega)).trans
      (byteMemoryPrefix_writeWord _ 64 (ptr + 32) _ (.inr (by decide))))
  exact h0.preserve hp (by rw [UInt256.toNat_ofNat_of_lt hptr]; exact hlo)
    (by rw [UInt256.toNat_ofNat_of_lt hptr, ByteArray.size_empty])

theorem constructorLiteralMemory_empty1 (mem : ByteArray) (ptr : Nat)
    (hlo : 96 ≤ ptr) (hptr : ptr + 32 < UInt256.size) :
    BytesBuffer (constructorLiteralMemory mem ptr) (UInt256.ofNat (ptr + 32)) ByteArray.empty := by
  have h1 := emptyLiteralMemory_buffer (emptyLiteralMemory mem ptr) (ptr + 32) hptr
  have hp : ByteMemoryPrefix (emptyLiteralMemory (emptyLiteralMemory mem ptr) (ptr + 32))
      (constructorLiteralMemory mem ptr) (ptr + 64) :=
    (emptyLiteralMemory_prefix _ (ptr + 64)).trans
    (byteMemoryPrefix_writeWord _ 64 (ptr + 64) _ (.inr (by decide)))
  exact h1.preserve hp (by rw [UInt256.toNat_ofNat_of_lt hptr]; omega)
    (by rw [UInt256.toNat_ofNat_of_lt hptr, ByteArray.size_empty])

theorem constructorLiteralMemory_empty2 (mem : ByteArray) (ptr : Nat)
    (hlo : 96 ≤ ptr) (hptr : ptr + 64 < UInt256.size) :
    BytesBuffer (constructorLiteralMemory mem ptr) (UInt256.ofNat (ptr + 64)) ByteArray.empty := by
  have h2 := emptyLiteralMemory_buffer
    (emptyLiteralMemory (emptyLiteralMemory mem ptr) (ptr + 32)) (ptr + 64) hptr
  exact h2.writeWord 64 _ (.inr (by rw [UInt256.toNat_ofNat_of_lt hptr]; omega))

theorem constructorLiteralMemory_empty (mem : ByteArray) (ptr : Nat) (i : Fin 3)
    (hlo : 96 ≤ ptr) (hptr : ptr + 64 < UInt256.size) :
    BytesBuffer (constructorLiteralMemory mem ptr) (UInt256.ofNat (ptr + 32 * i.val))
      ByteArray.empty := by
  fin_cases i
  · exact constructorLiteralMemory_empty0 mem ptr hlo (by omega)
  · exact constructorLiteralMemory_empty1 mem ptr hlo (by omega)
  · exact constructorLiteralMemory_empty2 mem ptr hlo hptr

def constructorVersionMemory (mem : ByteArray) (ptr : Nat) : ByteArray :=
  writeWord (writeWord (constructorLiteralMemory mem ptr) (ptr + 96) ⟨1⟩)
    (ptr + 128) (UInt256.shiftLeft (UInt256.ofNat 49) (UInt256.ofNat 248))

theorem constructorVersionMemory_empty (mem : ByteArray) (ptr : Nat) (i : Fin 3)
    (hlo : 96 ≤ ptr) (hptr : ptr + 160 < UInt256.size) :
    BytesBuffer (constructorVersionMemory mem ptr) (UInt256.ofNat (ptr + 32 * i.val))
      ByteArray.empty := by
  have hi := i.isLt
  have hw : ptr + 32 * i.val < UInt256.size := by omega
  have h0 := constructorLiteralMemory_empty mem ptr i hlo (by omega)
  have h1 := h0.writeWord (ptr + 96) ⟨1⟩ (.inl (by
    rw [UInt256.toNat_ofNat_of_lt hw, ByteArray.size_empty]; omega))
  exact h1.writeWord (ptr + 128) _ (.inl (by
    rw [UInt256.toNat_ofNat_of_lt hw, ByteArray.size_empty]; omega))

theorem constructorVersionMemory_prefix (mem : ByteArray) (ptr : Nat) :
    ByteMemoryPrefix mem (constructorVersionMemory mem ptr) ptr :=
  (constructorLiteralMemory_prefix mem ptr).trans
    ((byteMemoryPrefix_writeWord _ (ptr + 96) ptr ⟨1⟩ (.inl (by omega))).trans
      (byteMemoryPrefix_writeWord _ (ptr + 128) ptr _ (.inl (by omega))))

theorem constructorVersionMemory_free (mem : ByteArray) (ptr : Nat) :
    memLoad ⟨64⟩ (constructorVersionMemory mem ptr) = UInt256.ofNat (ptr + 160) := by
  apply loadedWord_of_read
  · change 64 + 32 ≤ _
    simp only [constructorVersionMemory, writeWord_sparse_size]; omega
  · change (constructorVersionMemory mem ptr).readWithPadding 64 32 = _
    rw [constructorVersionMemory,
      writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by omega, by
        rw [writeWord_sparse_size]; omega⟩),
      writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by omega, by
        rw [constructorLiteralMemory, writeWord_sparse_size]; omega⟩),
      constructorLiteralMemory, writeWord_sparse_read_back]

theorem constructorVersionMemory_version (mem : ByteArray) (ptr : Nat)
    (hptr : ptr + 160 < UInt256.size) :
    BytesBuffer (constructorVersionMemory mem ptr) (UInt256.ofNat (ptr + 96)) "1".toUTF8 := by
  have hp : ptr + 96 < UInt256.size := by omega
  have hbytes : "1".toUTF8.size = 1 := by decide
  refine ⟨?_, ?_, ?_⟩
  · rw [UInt256.toNat_ofNat_of_lt hp, hbytes, constructorVersionMemory, writeWord_sparse_size]
    omega
  · apply loadedWord_of_read
    · rw [UInt256.toNat_ofNat_of_lt hp, constructorVersionMemory, writeWord_sparse_size]
      omega
    · rw [UInt256.toNat_ofNat_of_lt hp, constructorVersionMemory,
        writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by omega, by
          rw [writeWord_sparse_size]; omega⟩), writeWord_sparse_read_back, hbytes]
      rfl
  · rw [UInt256.toNat_ofNat_of_lt hp, hbytes,
      show ptr + 96 + 32 = ptr + 128 by omega]
    have hr := writeWord_sparse_read_window
      (writeWord (constructorLiteralMemory mem ptr) (ptr + 96) ⟨1⟩) (ptr + 128) 0 1
      (UInt256.shiftLeft (UInt256.ofNat 49) (UInt256.ofNat 248)) (by decide) (by decide) (by decide)
    change (constructorVersionMemory mem ptr).readWithPadding (ptr + 128 + 0) 1 = _ at hr
    exact hr.trans (by native_decide)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
