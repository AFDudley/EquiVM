import Benchmarks.Safe.V1_0227664.ContractSignatureSource
import Benchmarks.Safe.V1_0227664.WordBytesEncoding

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V1_0227664

def contractSignatureCallLength (len : Nat) : Nat := 100 + ABI.paddedSize len

def contractSignatureCallEnd (ptr len : Nat) : Nat := ptr + contractSignatureCallLength len

def contractSignatureHeaderMemory (mem : ByteArray) (ptr : Nat) (hash : UInt256) : ByteArray :=
  writeWords (writeWord mem ptr signatureMagicWord) (ptr + 4) [hash, ⟨64⟩]

def contractSignatureCallMemory (mem : ByteArray) (ptr len : Nat) (hash : UInt256)
    (words : List UInt256) : ByteArray :=
  wordBytesArgsMemory (writeWord mem ptr signatureMagicWord) (ptr + 4) len hash words

theorem contractSignatureCallMemory_size (mem : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32) :
    (contractSignatureCallMemory mem ptr len hash words).size =
      max mem.size (ptr + 132 + len) := by
  rw [contractSignatureCallMemory, wordBytesArgsMemory_size _ _ _ _ _ hn,
    writeWord_sparse_size]
  omega

theorem contractSignatureCallMemory_preserved (mem : ByteArray) (ptr len off count : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hin : off + count ≤ mem.size) (hl : 96 ≤ off) (hh : off + count ≤ ptr) :
    (contractSignatureCallMemory mem ptr len hash words).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [contractSignatureCallMemory, wordBytesArgsMemory_preserved _ _ _ _ _ _ _
    (by rw [writeWord_sparse_size]; omega) (by omega),
    writeWordReadBelow _ _ _ _ _ hin hh]

theorem contractSignatureCallMemory_free (mem : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (contractSignatureCallMemory mem ptr len hash words) = memLoad ⟨64⟩ mem := by
  rw [memLoadReadWord, show (⟨64⟩ : UInt256).toNat = 64 from rfl,
    contractSignatureCallMemory, wordBytesArgsMemory_preserved _ _ _ _ _ _ _
      (by rw [writeWord_sparse_size]; omega) (by omega),
    writeWordReadBelow _ _ _ _ _ hm hp,
    ← show (⟨64⟩ : UInt256).toNat = 64 from rfl, ← memLoadReadWord]

theorem contractSignatureCallMemory_read (mem : ByteArray) (ptr : Nat)
    (hash : UInt256) (signature : ByteArray) (words : List UInt256)
    (hn : words.length = (signature.size + 31) / 32) (hp : 96 ≤ ptr)
    (hb : ptr + 32 < UInt256.size)
    (hs : (wordBytes words).extract 0 signature.size = signature) :
    (contractSignatureCallMemory mem ptr signature.size hash words).readWithPadding
      ptr (contractSignatureCallLength signature.size) =
      contractSignatureCallBytes hash signature := by
  have hsize := contractSignatureCallMemory_size mem ptr signature.size hash words hn
  have hsel : (contractSignatureCallMemory mem ptr signature.size hash words).readWithPadding
      ptr 4 = isValidSignatureSelector := by
    rw [contractSignatureCallMemory, wordBytesArgsMemory_preserved _ _ _ _ _ _ _
      (by rw [writeWord_sparse_size]; omega) (by omega)]
    have hr := writeWord_sparse_read_window mem ptr 0 4 signatureMagicWord
      (by decide) (by decide) (by decide)
    simpa only [Nat.add_zero, Nat.zero_add,
      show signatureMagicWord.toByteArray.extract 0 4 = isValidSignatureSelector
        from by decide +kernel] using hr
  have ht := wordBytesArgsMemory_read (writeWord mem ptr signatureMagicWord) (ptr + 4)
    signature.size hash words hn
  have hlen : contractSignatureCallLength signature.size = 4 + (96 + 32 * words.length) := by
    rw [contractSignatureCallLength, ABI.paddedSize, hn]
    omega
  rw [hlen, byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by omega)
      (by rw [hn] at *; omega), hsel]
  change isValidSignatureSelector ++ (wordBytesArgsMemory _ _ _ _ _).readWithPadding _ _ = _
  rw [ht, hs]
  simp only [contractSignatureCallBytes, ABI.paddedSize, hn, ByteArray.append_assoc]

end Benchmarks.Safe.V1_0227664
