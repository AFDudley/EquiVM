import Benchmarks.Safe.ViaIR.EcrecoverSource
import Benchmarks.Safe.ViaIR.WordWrites
import Benchmarks.Safe.ViaIR.ByteCopy
import Benchmarks.Safe.ViaIR.GuardCallMemory
import Benchmarks.Safe.ViaIR.MemoryBytesDecoded

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

def ecrecoverInputMemory (mem : ByteArray) (ptr : Nat) (p : EcrecoverInput) : ByteArray :=
  writeWord (writeWords mem ptr (ecrecoverWords p)) 0 ⟨0⟩

def ecrecoverOutputMemory (mem : ByteArray) (ptr : Nat) (p : EcrecoverInput)
    (out : ByteArray) : ByteArray :=
  out.write 0 (ecrecoverInputMemory mem ptr p) 0 (min 32 out.size)

theorem ecrecoverInputMemory_size (mem : ByteArray) (ptr : Nat) (p : EcrecoverInput) :
    (ecrecoverInputMemory mem ptr p).size = max mem.size (ptr + 128) := by
  rw [ecrecoverInputMemory, writeWord_sparse_size,
    writeWords_size_nonempty _ _ _ (by simp [ecrecoverWords])]
  simp only [ecrecoverWords, List.length_cons, List.length_nil]
  omega

theorem ecrecoverInputMemory_read (mem : ByteArray) (ptr : Nat) (p : EcrecoverInput)
    (hp : 32 ≤ ptr) :
    (ecrecoverInputMemory mem ptr p).readWithPadding ptr 128 = wordBytes (ecrecoverWords p) := by
  rw [ecrecoverInputMemory, writeWordReadAbove _ _ _ _ _ (by
    rw [writeWords_size_nonempty _ _ _ (by simp [ecrecoverWords])]
    simp [ecrecoverWords]) hp]
  exact writeWords_read _ _ _

theorem ecrecoverInputMemory_free (mem : ByteArray) (ptr : Nat) (p : EcrecoverInput)
    (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (ecrecoverInputMemory mem ptr p) = memLoad ⟨64⟩ mem := by
  rw [memLoadReadWord, show (⟨64⟩ : UInt256).toNat = 64 from rfl,
    ecrecoverInputMemory, writeWordReadAbove _ _ _ _ _ (by
      rw [writeWords_size_nonempty _ _ _ (by simp [ecrecoverWords])]; omega) (by decide),
    writeWords_readBelow _ _ _ _ _ hm hp]
  rw [memLoadReadWord]
  rfl

theorem ecrecoverInputMemory_zero (mem : ByteArray) (ptr : Nat) (p : EcrecoverInput) :
    (ecrecoverInputMemory mem ptr p).readWithPadding 0 32 = (⟨0⟩ : UInt256).toByteArray :=
  writeWord_sparse_read_back _ _ _

theorem ecrecoverInputMemory_preserved (mem : ByteArray) (ptr off count : Nat)
    (p : EcrecoverInput) (hin : off + count ≤ mem.size) (hl : 32 ≤ off)
    (hh : off + count ≤ ptr) :
    (ecrecoverInputMemory mem ptr p).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [ecrecoverInputMemory, writeWordReadAbove _ _ _ _ _ (by
    rw [writeWords_size_nonempty _ _ _ (by simp [ecrecoverWords])]; omega) hl,
    writeWords_readBelow _ _ _ _ _ hin hh]

theorem ecrecoverOutputMemory_size (mem out : ByteArray) (ptr : Nat) (p : EcrecoverInput) :
    (ecrecoverOutputMemory mem ptr p out).size = max mem.size (ptr + 128) := by
  by_cases hz : out.size = 0
  · simp only [ecrecoverOutputMemory, hz, Nat.min_zero, byteArray_write_zero_length,
      ecrecoverInputMemory_size]
  rw [ecrecoverOutputMemory, copyWindow_size _ _ _ _ _ (by omega) (by omega)
    (Nat.zero_le _), ecrecoverInputMemory_size]
  omega

theorem ecrecoverOutputMemory_preserved (mem out : ByteArray) (ptr off count : Nat)
    (p : EcrecoverInput) (hin : off + count ≤ mem.size) (hl : 32 ≤ off)
    (hh : off + count ≤ ptr) :
    (ecrecoverOutputMemory mem ptr p out).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [ecrecoverOutputMemory, copyWindowReadAbove _ _ _ _ _ _ _ (by omega)
    (Nat.zero_le _) (by rw [ecrecoverInputMemory_size]; omega) (by omega),
    ecrecoverInputMemory_preserved _ _ _ _ _ hin hl hh]

theorem ecrecoverOutputMemory_free (mem out : ByteArray) (ptr : Nat) (p : EcrecoverInput)
    (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (ecrecoverOutputMemory mem ptr p out) = memLoad ⟨64⟩ mem := by
  rw [memLoadReadWord, show (⟨64⟩ : UInt256).toNat = 64 from rfl,
    ecrecoverOutputMemory_preserved _ _ _ _ _ _ hm (by decide) hp]
  rw [memLoadReadWord]
  rfl

theorem ecrecoverOutputMemory_word (mem out : ByteArray) (ptr : Nat) (p : EcrecoverInput)
    (ho : EcrecoverOutput out) :
    memLoad ⟨0⟩ (ecrecoverOutputMemory mem ptr p out) = calldataWord out 0 := by
  apply memLoad_of_wordRead
  change (ecrecoverOutputMemory mem ptr p out).readWithPadding 0 32 = _
  rcases ho with rfl | ⟨hs, _⟩
  · simp only [ecrecoverOutputMemory, ByteArray.size_empty, Nat.min_zero,
      byteArray_write_zero_length, ecrecoverInputMemory_zero]
    decide +kernel
  · exact callOutputWordAt _ out 0 (Nat.zero_le _) (by omega)

end Benchmarks.Safe.ViaIR
