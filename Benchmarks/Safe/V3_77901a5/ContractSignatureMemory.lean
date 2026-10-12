import Benchmarks.Safe.V3_77901a5.ContractSignatureSource
import Benchmarks.Safe.V3_77901a5.WordBytesEncoding
import Benchmarks.Safe.V3_77901a5.SelectorPatchMemory
import Benchmarks.Safe.V3_77901a5.RawBytesEncode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V3_77901a5

def contractSignatureCallLength (len : Nat) : Nat := 100 + ABI.paddedSize len

def contractSignatureCallEnd (ptr len : Nat) : Nat := ptr + 32 + contractSignatureCallLength len

def contractSignatureHeaderMemory (mem : ByteArray) (ptr : Nat) (hash : UInt256) : ByteArray :=
  writeWords mem (ptr + 36) [hash, ⟨64⟩]

def contractSignatureArgsMemory (mem : ByteArray) (ptr len : Nat) (hash : UInt256)
    (words : List UInt256) : ByteArray := wordBytesArgsMemory mem (ptr + 36) len hash words

def contractSignatureStoredMemory (mem : ByteArray) (ptr len : Nat) (hash : UInt256)
    (words : List UInt256) : ByteArray :=
  writeWord (writeWord (contractSignatureArgsMemory mem ptr len hash words) ptr
    (UInt256.ofNat (contractSignatureCallLength len))) 64
      (UInt256.ofNat (contractSignatureCallEnd ptr len))

def contractSignatureBufferMemory (mem : ByteArray) (ptr len : Nat) (hash : UInt256)
    (words : List UInt256) : ByteArray :=
  signatureMagicWord.toByteArray.write 0
    (contractSignatureStoredMemory mem ptr len hash words) (ptr + 32) 4

def contractSignatureCallMemory (mem : ByteArray) (ptr len : Nat) (hash : UInt256)
    (words : List UInt256) : ByteArray :=
  rawBytesCopyMemory (contractSignatureBufferMemory mem ptr len hash words)
    ptr (contractSignatureCallEnd ptr len) (3 + (len + 31) / 32)

theorem contractSignatureCallLength_words (len : Nat) :
    contractSignatureCallLength len = 32 * (3 + (len + 31) / 32) + 4 := by
  dsimp [contractSignatureCallLength, ABI.paddedSize]
  omega

theorem contractSignatureArgsMemory_size (mem : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32) :
    (contractSignatureArgsMemory mem ptr len hash words).size =
      max mem.size (ptr + 164 + len) := by
  rw [contractSignatureArgsMemory, wordBytesArgsMemory_size _ _ _ _ _ hn]

theorem contractSignatureStoredMemory_size (mem : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32) :
    (contractSignatureStoredMemory mem ptr len hash words).size =
      max mem.size (ptr + 164 + len) := by
  rw [contractSignatureStoredMemory, writeWord_sparse_size, writeWord_sparse_size,
    contractSignatureArgsMemory_size _ _ _ _ _ hn]
  omega

theorem contractSignatureBufferMemory_size (mem : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32) :
    (contractSignatureBufferMemory mem ptr len hash words).size =
      max mem.size (ptr + 164 + len) := by
  rw [contractSignatureBufferMemory, byteArray_write_size_of_inBounds _ _ _ _
    (by rw [toByteArray_size]; decide)
    (by rw [contractSignatureStoredMemory_size _ _ _ _ _ hn]; omega),
    contractSignatureStoredMemory_size _ _ _ _ _ hn]

theorem contractSignatureBufferMemory_end (mem : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32) :
    contractSignatureCallEnd ptr len ≤ (contractSignatureBufferMemory mem ptr len hash words).size := by
  rw [contractSignatureBufferMemory_size _ _ _ _ _ hn]
  dsimp [contractSignatureCallEnd, contractSignatureCallLength, ABI.paddedSize]
  omega

theorem contractSignatureCallMemory_size (mem : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32) :
    (contractSignatureCallMemory mem ptr len hash words).size =
      max mem.size (ptr + 264 + 2 * ABI.paddedSize len) := by
  rw [contractSignatureCallMemory, rawBytesCopyMemory_size _ _ _ _
    (contractSignatureBufferMemory_end _ _ _ _ _ hn),
    contractSignatureBufferMemory_size _ _ _ _ _ hn]
  dsimp [contractSignatureCallEnd, contractSignatureCallLength, ABI.paddedSize]
  omega

theorem contractSignatureBufferMemory_preserved (mem : ByteArray) (ptr len off count : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hin : off + count ≤ mem.size) (hl : 96 ≤ off) (hh : off + count ≤ ptr) :
    (contractSignatureBufferMemory mem ptr len hash words).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [contractSignatureBufferMemory, copyWindowReadBelow _ _ _ _ _ _ _
      (by rw [toByteArray_size]; decide)
      (by rw [contractSignatureStoredMemory_size _ _ _ _ _ hn]; omega) (by omega),
    contractSignatureStoredMemory, writeWordReadAbove _ _ _ _ _ (by
      rw [writeWord_sparse_size, contractSignatureArgsMemory_size _ _ _ _ _ hn]; omega) hl,
    writeWordReadBelow _ _ _ _ _ (by
      rw [contractSignatureArgsMemory_size _ _ _ _ _ hn]; omega) hh,
    contractSignatureArgsMemory, wordBytesArgsMemory_preserved _ _ _ _ _ _ _ hin (by omega)]

theorem contractSignatureCallMemory_preserved (mem : ByteArray) (ptr len off count : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hin : off + count ≤ mem.size) (hl : 96 ≤ off) (hh : off + count ≤ ptr) :
    (contractSignatureCallMemory mem ptr len hash words).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [contractSignatureCallMemory, rawBytesCopyMemory_preserved _ _ _ _ _ _
    (contractSignatureBufferMemory_end _ _ _ _ _ hn)
    (by rw [contractSignatureBufferMemory_size _ _ _ _ _ hn]; omega)
    (by dsimp [contractSignatureCallEnd]; omega),
    contractSignatureBufferMemory_preserved _ _ _ _ _ _ _ hn hin hl hh]

theorem contractSignatureBufferMemory_free (mem : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (contractSignatureBufferMemory mem ptr len hash words) =
      UInt256.ofNat (contractSignatureCallEnd ptr len) := by
  apply memLoad_of_wordRead
  change (contractSignatureBufferMemory mem ptr len hash words).readWithPadding 64 32 = _
  rw [contractSignatureBufferMemory, copyWindowReadBelow _ _ _ _ _ _ _
      (by rw [toByteArray_size]; decide)
      (by rw [contractSignatureStoredMemory_size _ _ _ _ _ hn]; omega) (by omega),
    contractSignatureStoredMemory, writeWord_sparse_read_back]

theorem contractSignatureBufferMemory_length (mem : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hp : 96 ≤ ptr) (hb : ptr < UInt256.size) :
    memLoad (UInt256.ofNat ptr) (contractSignatureBufferMemory mem ptr len hash words) =
      UInt256.ofNat (contractSignatureCallLength len) := by
  apply memLoad_of_wordRead
  rw [ulit_toNat' _ hb, contractSignatureBufferMemory,
    copyWindowReadBelow _ _ _ _ _ _ _ (by rw [toByteArray_size]; decide)
      (by rw [contractSignatureStoredMemory_size _ _ _ _ _ hn]; omega) (by omega),
    contractSignatureStoredMemory, writeWordReadAbove _ _ _ _ _
      (by rw [writeWord_sparse_size]; omega) hp, writeWord_sparse_read_back]

theorem contractSignatureCallMemory_free (mem : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (contractSignatureCallMemory mem ptr len hash words) =
      UInt256.ofNat (contractSignatureCallEnd ptr len) := by
  rw [memLoadReadWord, show (⟨64⟩ : UInt256).toNat = 64 from rfl,
    contractSignatureCallMemory, rawBytesCopyMemory_preserved _ _ _ _ _ _
      (contractSignatureBufferMemory_end _ _ _ _ _ hn)
      (by rw [contractSignatureBufferMemory_size _ _ _ _ _ hn]; omega)
      (by dsimp [contractSignatureCallEnd]; omega),
    ← show (⟨64⟩ : UInt256).toNat = 64 from rfl, ← memLoadReadWord,
    contractSignatureBufferMemory_free _ _ _ _ _ hn hp]

theorem contractSignatureBufferMemory_read (mem : ByteArray) (ptr : Nat)
    (hash : UInt256) (signature : ByteArray) (words : List UInt256)
    (hn : words.length = (signature.size + 31) / 32) (hp : 96 ≤ ptr)
    (hs : (wordBytes words).extract 0 signature.size = signature) :
    (contractSignatureBufferMemory mem ptr signature.size hash words).readWithPadding
      (ptr + 32) (contractSignatureCallLength signature.size) =
      contractSignatureCallBytes hash signature := by
  have hsel : (contractSignatureBufferMemory mem ptr signature.size hash words).readWithPadding
      (ptr + 32) 4 = isValidSignatureSelector := by
    rw [contractSignatureBufferMemory, copySlice_read _ _ _ _ _
      (by rw [toByteArray_size]; decide)
      (by rw [contractSignatureStoredMemory_size _ _ _ _ _ hn]; omega)]
    decide +kernel
  have ht : (contractSignatureBufferMemory mem ptr signature.size hash words).readWithPadding
      (ptr + 36) (96 + 32 * words.length) =
      wordBytes [hash, ⟨64⟩, UInt256.ofNat signature.size] ++ signature ++
        ByteArray.zeroes (32 * words.length - signature.size) := by
    rw [contractSignatureBufferMemory, copyWindowReadAbove _ _ _ _ _ _ _
        (by rw [toByteArray_size]; decide)
        (by rw [contractSignatureStoredMemory_size _ _ _ _ _ hn]; omega)
        (by rw [contractSignatureStoredMemory_size _ _ _ _ _ hn, hn]; omega) (by omega),
      contractSignatureStoredMemory, writeWordReadAbove _ _ _ _ _
        (by rw [writeWord_sparse_size, contractSignatureArgsMemory_size _ _ _ _ _ hn, hn]; omega)
        (by omega), writeWordReadAbove _ _ _ _ _
        (by rw [contractSignatureArgsMemory_size _ _ _ _ _ hn, hn]; omega) (by omega),
      contractSignatureArgsMemory, wordBytesArgsMemory_read _ _ _ _ _ hn, hs]
  have hlen : contractSignatureCallLength signature.size = 4 + (96 + 32 * words.length) := by
    rw [contractSignatureCallLength, ABI.paddedSize, hn]
    omega
  rw [hlen, byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by omega)
      (by rw [contractSignatureBufferMemory_size _ _ _ _ _ hn, hn]; omega), hsel,
    show ptr + 32 + 4 = ptr + 36 by omega, ht]
  simp only [contractSignatureCallBytes, ABI.paddedSize, hn, ByteArray.append_assoc]

theorem contractSignatureCallMemory_read (mem : ByteArray) (ptr : Nat)
    (hash : UInt256) (signature : ByteArray) (words : List UInt256)
    (hn : words.length = (signature.size + 31) / 32) (hp : 96 ≤ ptr)
    (hb : ptr + 32 < UInt256.size)
    (hs : (wordBytes words).extract 0 signature.size = signature) :
    (contractSignatureCallMemory mem ptr signature.size hash words).readWithPadding
      (contractSignatureCallEnd ptr signature.size) (contractSignatureCallLength signature.size) =
      contractSignatureCallBytes hash signature := by
  rw [contractSignatureCallMemory, contractSignatureCallLength_words,
    rawBytesCopyMemory_read _ _ _ _ (contractSignatureBufferMemory_end _ _ _ _ _ hn)
      (by omega)
      (by rw [contractSignatureBufferMemory_size _ _ _ _ _ hn]; omega)
      (by dsimp [contractSignatureCallEnd]; rw [contractSignatureCallLength_words]; omega),
    ← contractSignatureCallLength_words, contractSignatureBufferMemory_read _ _ _ _ _ hn hp hs]

end Benchmarks.Safe.V3_77901a5
