import Benchmarks.Safe.V2_0e91d99.P256Source
import Benchmarks.Safe.V2_0e91d99.WordWrites
import Benchmarks.Safe.V2_0e91d99.ByteCopy
import Benchmarks.Safe.V2_0e91d99.GuardCallMemory
import Benchmarks.Safe.V2_0e91d99.MemoryPreserves

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V2_0e91d99

def p256InputMemory (mem : ByteArray) (ptr : Nat) (p : P256Input) : ByteArray :=
  writeWords mem ptr p.words

def p256OutputMemory (mem : ByteArray) (ptr : Nat) (p : P256Input) (out : ByteArray) : ByteArray :=
  out.write 0 (p256InputMemory mem ptr p) 0 (min 32 out.size)

theorem p256InputMemory_size (mem : ByteArray) (ptr : Nat) (p : P256Input) :
    (p256InputMemory mem ptr p).size = max mem.size (ptr + 160) := by
  rw [p256InputMemory, writeWords_size_nonempty _ _ _ (by simp [P256Input.words])]
  simp [P256Input.words]

theorem p256InputMemory_read (mem : ByteArray) (ptr : Nat) (p : P256Input) :
    (p256InputMemory mem ptr p).readWithPadding ptr 160 = wordBytes p.words :=
  writeWords_read _ _ _

theorem p256OutputMemory_size (mem out : ByteArray) (ptr : Nat) (p : P256Input) :
    (p256OutputMemory mem ptr p out).size = max mem.size (ptr + 160) := by
  by_cases hz : out.size = 0
  · simp only [p256OutputMemory, hz, Nat.min_zero, byteArray_write_zero_length,
      p256InputMemory_size]
  rw [p256OutputMemory, copyWindow_size _ _ _ _ _ (by omega) (by omega) (by omega),
    p256InputMemory_size]
  omega

theorem p256OutputMemory_read_preserved (mem out : ByteArray) (ptr off count : Nat)
    (p : P256Input) (hin : off + count ≤ mem.size) (hl : 32 ≤ off)
    (hh : off + count ≤ ptr) :
    (p256OutputMemory mem ptr p out).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [p256OutputMemory, copyWindowReadAbove _ _ _ _ _ _ _ (by omega) (by omega)
    (by rw [p256InputMemory_size]; omega) (by omega),
    p256InputMemory, writeWords_readBelow _ _ _ _ _ hin hh]

theorem p256OutputMemory_preserves (mem out : ByteArray) (ptr : Nat) (p : P256Input) :
    MemoryPreserves mem (p256OutputMemory mem ptr p out) 32 ptr := by
  refine ⟨?_, fun off count hl hh hin ↦ p256OutputMemory_read_preserved _ _ _ _ _ _ hin hl hh⟩
  rw [p256OutputMemory_size]
  omega

theorem p256OutputMemory_free (mem out : ByteArray) (ptr : Nat) (p : P256Input)
    (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (p256OutputMemory mem ptr p out) = memLoad ⟨64⟩ mem :=
  (p256OutputMemory_preserves mem out ptr p).load _ (by decide) hp hm

theorem p256OutputMemory_zero (mem out : ByteArray) (ptr : Nat) (p : P256Input)
    (hm : 128 ≤ mem.size) (hp : 128 ≤ ptr) :
    memLoad ⟨96⟩ (p256OutputMemory mem ptr p out) = memLoad ⟨96⟩ mem :=
  (p256OutputMemory_preserves mem out ptr p).load _ (by decide) hp hm

theorem p256OutputMemory_bytes {mem bytes : ByteArray} {ptr src : Nat}
    (h : BytesMemory mem src bytes) (out : ByteArray) (p : P256Input)
    (hb : src < UInt256.size) (hs : 32 ≤ src) (hp : src + 32 + bytes.size ≤ ptr) :
    BytesMemory (p256OutputMemory mem ptr p out) src bytes := by
  apply h.preserved hb (p256OutputMemory_preserves mem out ptr p).size
  intro off count hl hh
  exact p256OutputMemory_read_preserved mem out ptr off count p
    (by have := h.available; omega) (by omega) (by omega)

theorem p256OutputMemory_word (mem out : ByteArray) (ptr : Nat) (p : P256Input)
    (ho : 32 ≤ out.size) :
    memLoad ⟨0⟩ (p256OutputMemory mem ptr p out) = calldataWord out 0 := by
  apply memLoad_of_wordRead
  exact callOutputWordAt _ _ 0 (by omega) ho

end Benchmarks.Safe.V2_0e91d99
