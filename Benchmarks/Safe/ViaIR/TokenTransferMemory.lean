import Benchmarks.Safe.ViaIR.TokenTransferSource
import Benchmarks.Safe.ViaIR.SelectorWordsMemory
import Benchmarks.Safe.ViaIR.MemoryPreserves

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

def transferSelectorWord : UInt256 := UInt256.shiftLeft ⟨2835717307⟩ ⟨224⟩

def tokenTransferArgsMemory (mem : ByteArray) (ptr : Nat) (receiver amount : UInt256) :
    ByteArray :=
  writeWord (writeWord mem (ptr + 36) receiver) (ptr + 68) amount

def tokenTransferHeaderMemory (mem : ByteArray) (ptr : Nat) (receiver amount : UInt256) :
    ByteArray :=
  writeWord (tokenTransferArgsMemory (writeWord mem (ptr + 32) transferSelectorWord)
    ptr receiver amount) ptr ⟨68⟩

def tokenTransferMemory (mem : ByteArray) (ptr : Nat) (receiver amount : UInt256) :
    ByteArray :=
  writeWord (tokenTransferHeaderMemory mem ptr receiver amount) 64 (UInt256.ofNat (ptr + 128))

theorem tokenTransferArgsMemory_size (mem : ByteArray) (ptr : Nat)
    (receiver amount : UInt256) :
    (tokenTransferArgsMemory mem ptr receiver amount).size = max mem.size (ptr + 100) := by
  simp only [tokenTransferArgsMemory, writeWord_sparse_size]
  omega

theorem tokenTransferHeaderMemory_size (mem : ByteArray) (ptr : Nat)
    (receiver amount : UInt256) :
    (tokenTransferHeaderMemory mem ptr receiver amount).size = max mem.size (ptr + 100) := by
  simp only [tokenTransferHeaderMemory, writeWord_sparse_size, tokenTransferArgsMemory_size]
  omega

theorem tokenTransferMemory_size (mem : ByteArray) (ptr : Nat) (receiver amount : UInt256) :
    (tokenTransferMemory mem ptr receiver amount).size = max mem.size (ptr + 100) := by
  simp only [tokenTransferMemory, writeWord_sparse_size, tokenTransferHeaderMemory_size]
  omega

theorem tokenTransferArgsMemory_preserved (mem : ByteArray) (ptr off count : Nat)
    (receiver amount : UInt256) (hin : off + count ≤ mem.size) (hh : off + count ≤ ptr) :
    (tokenTransferArgsMemory mem ptr receiver amount).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [tokenTransferArgsMemory, writeWordReadBelow _ _ _ _ _ (by
    rw [writeWord_sparse_size]; omega) (by omega),
    writeWordReadBelow _ _ _ _ _ hin (by omega)]

theorem tokenTransferArgsMemory_free {mem : ByteArray} {ptr : Nat} {receiver amount : UInt256}
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (tokenTransferArgsMemory mem ptr receiver amount) = UInt256.ofNat ptr := by
  rw [memLoadReadWord, show (⟨64⟩ : UInt256).toNat = 64 from rfl,
    tokenTransferArgsMemory_preserved _ _ _ _ _ _ hm hp,
    ← show (⟨64⟩ : UInt256).toNat = 64 from rfl, ← memLoadReadWord, hf]

theorem tokenTransferMemory_free (mem : ByteArray) (ptr : Nat) (receiver amount : UInt256)
    (_hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (tokenTransferMemory mem ptr receiver amount) = UInt256.ofNat (ptr + 128) := by
  apply memLoad_of_wordRead
  exact writeWord_sparse_read_back _ _ _

theorem tokenTransferMemory_length (mem : ByteArray) (ptr : Nat) (receiver amount : UInt256)
    (hp : 96 ≤ ptr) :
    (tokenTransferMemory mem ptr receiver amount).readWithPadding ptr 32 =
      (⟨68⟩ : UInt256).toByteArray := by
  rw [tokenTransferMemory, writeWordReadAbove _ _ _ _ _ (by
    rw [tokenTransferHeaderMemory_size]; omega) hp, tokenTransferHeaderMemory,
    writeWord_sparse_read_back]

theorem tokenTransferMemory_preserved (mem : ByteArray) (ptr : Nat) (receiver amount : UInt256) :
    MemoryPreserves mem (tokenTransferMemory mem ptr receiver amount) 96 ptr := by
  refine ⟨by rw [tokenTransferMemory_size]; omega, ?_⟩
  intro off count hl hh hin
  rw [tokenTransferMemory, writeWordReadAbove _ _ _ _ _ (by
      rw [tokenTransferHeaderMemory_size]; omega) hl,
    tokenTransferHeaderMemory, writeWordReadBelow _ _ _ _ _ (by
      rw [tokenTransferArgsMemory_size]; omega) hh,
    tokenTransferArgsMemory_preserved _ _ _ _ _ _ (by rw [writeWord_sparse_size]; omega) hh,
    writeWordReadBelow _ _ _ _ _ hin (by omega)]

theorem tokenTransferMemory_read (mem : ByteArray) (ptr : Nat) (receiver amount : UInt256)
    (hp : 96 ≤ ptr) :
    (tokenTransferMemory mem ptr receiver amount).readWithPadding (ptr + 32) 68 =
      transferSelector ++ receiver.toByteArray ++ amount.toByteArray := by
  rw [tokenTransferMemory, writeWordReadAbove _ _ _ _ _ (by
      rw [tokenTransferHeaderMemory_size]; omega) (by omega),
    tokenTransferHeaderMemory, writeWordReadAbove _ _ _ _ _ (by
      rw [tokenTransferArgsMemory_size]; omega) (by omega)]
  have hs : transferSelectorWord.toByteArray.extract 0 4 = transferSelector := by decide +kernel
  simpa only [selectorWordPairMemory, tokenTransferArgsMemory, Nat.add_assoc, hs] using
    selectorWordPairMemory_read mem (ptr + 32) transferSelectorWord receiver amount

end Benchmarks.Safe.ViaIR
