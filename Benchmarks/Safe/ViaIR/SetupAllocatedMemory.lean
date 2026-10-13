import Benchmarks.Safe.ViaIR.SetupEventMemory
import Benchmarks.Safe.ViaIR.CalldataBufferMemory
import Benchmarks.Safe.ViaIR.WordWrites
import Benchmarks.Safe.ViaIR.SetupCalldataFacts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

def setupEventInitialMemory (cd : ByteArray) (n : Nat) : ByteArray :=
  setupEventMemory solcFreePtrMem 128 (calldataWords cd (setupOwnersStart cd) n)
    (calldataWord cd 36) (calldataWord cd 68) (calldataWord cd 132)

def setupOwnersAllocatedMemory (cd : ByteArray) (n : Nat) : ByteArray :=
  writeWords (calldataBufferHeader (setupEventInitialMemory cd n) 128 n (160 + 32 * n)) 160
    (calldataWords cd (setupOwnersStart cd) n)

theorem setupEventInitialMemory_size (cd : ByteArray) (n : Nat) :
    (setupEventInitialMemory cd n).size = 288 + 32 * n := by
  rw [setupEventInitialMemory, setupEventMemory_size _ _ _ _ _ _
    (by rw [solcFreePtrMem_size]; decide), calldataWords_length]

theorem setupEventInitialMemory_free (cd : ByteArray) (n : Nat) :
    memLoad ⟨64⟩ (setupEventInitialMemory cd n) = ⟨128⟩ := by
  rw [setupEventInitialMemory, setupEventMemory_load _ _ _ _ _ _ _
    (by rw [solcFreePtrMem_size]; decide) (by decide)
    (.inl (by rw [solcFreePtrMem_size]; decide))]
  exact solcFreePtrMem_mload64

theorem setupEventInitialMemory_zero (cd : ByteArray) (n : Nat) :
    memLoad ⟨96⟩ (setupEventInitialMemory cd n) = ⟨0⟩ := by
  rw [setupEventInitialMemory, setupEventMemory_load _ _ _ _ _ _ _
    (by rw [solcFreePtrMem_size]; decide) (by decide)
    (.inr (by rw [solcFreePtrMem_size]; decide))]
  apply memLoad_of_wordRead
  rw [readPastMemory _ _ _ (by rw [solcFreePtrMem_size]; decide)]
  decide +kernel

theorem setupOwnersAllocatedMemory_size {cd : ByteArray} {n : Nat}
    (hs : setupOwnersStart cd + 32 * n ≤ cd.size) :
    (setupOwnersAllocatedMemory cd n).size = 288 + 32 * n := by
  have hh : (calldataBufferHeader (setupEventInitialMemory cd n) 128 n (160 + 32 * n)).size =
      288 + 32 * n := by
    rw [calldataBufferHeader_size _ _ _ _ (by rw [setupEventInitialMemory_size]; omega),
      setupEventInitialMemory_size]
    omega
  rw [setupOwnersAllocatedMemory, writeWords_size _ _ _ (by rw [hh]; omega), hh,
    calldataWords_length]
  omega

theorem setupOwnersAllocatedMemory_free {cd : ByteArray} {n : Nat}
    (hs : setupOwnersStart cd + 32 * n ≤ cd.size) :
    memLoad ⟨64⟩ (setupOwnersAllocatedMemory cd n) = UInt256.ofNat (160 + 32 * n) := by
  apply memLoad_of_wordRead
  change (setupOwnersAllocatedMemory cd n).readWithPadding 64 32 = _
  rw [setupOwnersAllocatedMemory, writeWords_readBelow _ _ _ _ _
    (by simp only [calldataBufferHeader, writeWord_sparse_size]; omega) (by decide),
    calldataBufferHeader, writeWordReadBelow _ _ _ _ _
      (by rw [writeWord_sparse_size]; omega) (by decide), writeWord_sparse_read_back]

theorem setupOwnersAllocatedMemory_zero {cd : ByteArray} {n : Nat}
    (hs : setupOwnersStart cd + 32 * n ≤ cd.size) :
    memLoad ⟨96⟩ (setupOwnersAllocatedMemory cd n) = ⟨0⟩ := by
  have he : memLoad ⟨96⟩ (setupOwnersAllocatedMemory cd n) =
      memLoad ⟨96⟩ (setupEventInitialMemory cd n) := by
    rw [memLoadReadWord, memLoadReadWord]
    congr 1
    change (setupOwnersAllocatedMemory cd n).readWithPadding 96 32 = _
    rw [setupOwnersAllocatedMemory, writeWords_readBelow _ _ _ _ _
      (by simp only [calldataBufferHeader, writeWord_sparse_size]; omega) (by decide),
      calldataBufferHeader, writeWordReadBelow _ _ _ _ _
        (by rw [writeWord_sparse_size, setupEventInitialMemory_size]; omega) (by decide),
      writeWordReadAbove _ _ _ _ _ (by rw [setupEventInitialMemory_size]; omega) (by decide)]
    rfl
  exact he.trans (setupEventInitialMemory_zero cd n)

theorem setupOwnersAllocatedMemory_words {cd : ByteArray} {n : Nat}
    (hs : setupOwnersStart cd + 32 * n ≤ cd.size) :
    WordArrayBuffer (setupOwnersAllocatedMemory cd n) 128
      (calldataWords cd (setupOwnersStart cd) n) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [setupOwnersAllocatedMemory_size hs, calldataWords_length]; omega
  · rw [calldataWords_length, setupOwnersAllocatedMemory, writeWords_readBelow _ _ _ _ _
      (by simp only [calldataBufferHeader, writeWord_sparse_size]; omega) (by decide),
      calldataBufferHeader, writeWord_sparse_read_back]
  · exact writeWords_view _ _ _

end Benchmarks.Safe.ViaIR
