import Benchmarks.Safe.ViaIR.ContractSignatureSource
import Benchmarks.Safe.ViaIR.WordBytesEncoding

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

def contractSignatureCallLength (len : Nat) : Nat := 100 + ABI.paddedSize len

def contractSignatureCallEnd (ptr len : Nat) : Nat := ptr + 160 + ABI.paddedSize len

def contractSignatureHeaderMemory (mem : ByteArray) (ptr len : Nat) (hash : UInt256)
    (words : List UInt256) : ByteArray :=
  writeWord (writeWord (wordBytesArgsMemory (writeWord mem (ptr + 32) signatureMagicWord)
    (ptr + 36) len hash words) ptr
    (UInt256.ofNat (contractSignatureCallLength len))) 64
    (UInt256.ofNat (contractSignatureCallEnd ptr len))

def contractSignatureEncodedMemory (mem : ByteArray) (ptr len : Nat) (hash : UInt256)
    (words : List UInt256) : ByteArray :=
  contractSignatureHeaderMemory mem ptr len hash words

theorem contractSignatureHeaderMemory_size (mem : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32) :
    (contractSignatureHeaderMemory mem ptr len hash words).size =
      max mem.size (ptr + 164 + len) := by
  simp only [contractSignatureHeaderMemory, writeWord_sparse_size,
    wordBytesArgsMemory_size _ _ _ _ _ hn, writeWord_sparse_size]
  omega

theorem contractSignatureEncodedMemory_size (mem : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32) :
    (contractSignatureEncodedMemory mem ptr len hash words).size =
      max mem.size (ptr + 164 + len) := by
  exact contractSignatureHeaderMemory_size mem ptr len hash words hn

theorem contractSignatureEncodedMemory_free (mem : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (contractSignatureEncodedMemory mem ptr len hash words) =
      UInt256.ofNat (contractSignatureCallEnd ptr len) := by
  apply memLoad_of_wordRead
  exact writeWord_sparse_read_back _ _ _

theorem contractSignatureEncodedMemory_length (mem : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hp : 96 ≤ ptr) :
    (contractSignatureEncodedMemory mem ptr len hash words).readWithPadding ptr 32 =
      (UInt256.ofNat (contractSignatureCallLength len)).toByteArray := by
  rw [contractSignatureEncodedMemory, contractSignatureHeaderMemory,
    writeWordReadAbove _ _ _ _ _ (by rw [writeWord_sparse_size]; omega) hp,
    writeWord_sparse_read_back]

theorem contractSignatureEncodedMemory_preserved (mem : ByteArray) (ptr len off count : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hin : off + count ≤ mem.size) (hl : 96 ≤ off) (hh : off + count ≤ ptr) :
    (contractSignatureEncodedMemory mem ptr len hash words).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [contractSignatureEncodedMemory, contractSignatureHeaderMemory,
    writeWordReadAbove _ _ _ _ _ (by
      rw [writeWord_sparse_size, wordBytesArgsMemory_size _ _ _ _ _ hn,
        writeWord_sparse_size]; omega) hl,
    writeWordReadBelow _ _ _ _ _ (by
      rw [wordBytesArgsMemory_size _ _ _ _ _ hn, writeWord_sparse_size]; omega) hh,
    wordBytesArgsMemory_preserved _ _ _ _ _ _ _ (by rw [writeWord_sparse_size]; omega)
      (by omega), writeWordReadBelow _ _ _ _ _ hin (by omega)]

theorem contractSignatureEncodedMemory_read (mem : ByteArray) (ptr : Nat)
    (hash : UInt256) (signature : ByteArray) (words : List UInt256)
    (hn : words.length = (signature.size + 31) / 32) (hp : 96 ≤ ptr)
    (hs : (wordBytes words).extract 0 signature.size = signature) :
    (contractSignatureEncodedMemory mem ptr signature.size hash words).readWithPadding
      (ptr + 32) (contractSignatureCallLength signature.size) =
      contractSignatureCallBytes hash signature := by
  have hsize := contractSignatureEncodedMemory_size mem ptr signature.size hash words hn
  have hsel : (contractSignatureEncodedMemory mem ptr signature.size hash words).readWithPadding
      (ptr + 32) 4 = isValidSignatureSelector := by
    rw [contractSignatureEncodedMemory, contractSignatureHeaderMemory,
      writeWordReadAbove _ _ _ _ _ (by
        rw [writeWord_sparse_size, wordBytesArgsMemory_size _ _ _ _ _ hn,
          writeWord_sparse_size]; omega) (by omega),
      writeWordReadAbove _ _ _ _ _ (by
        rw [wordBytesArgsMemory_size _ _ _ _ _ hn, writeWord_sparse_size]; omega) (by omega),
      wordBytesArgsMemory_preserved _ _ _ _ _ _ _ (by rw [writeWord_sparse_size]; omega)
        (by omega),
      ← paddedReadPrefix _ (ptr + 32) 4 32 (by rw [writeWord_sparse_size]; omega)
        (by decide),
      writeWord_sparse_read_back]
    decide +kernel
  have ht : (contractSignatureEncodedMemory mem ptr signature.size hash words).readWithPadding
      (ptr + 36) (96 + 32 * words.length) =
      wordBytes [hash, ⟨64⟩, UInt256.ofNat signature.size] ++ signature ++
        ByteArray.zeroes (32 * words.length - signature.size) := by
    rw [contractSignatureEncodedMemory, contractSignatureHeaderMemory,
      writeWordReadAbove _ _ _ _ _ (by
        rw [writeWord_sparse_size, wordBytesArgsMemory_size _ _ _ _ _ hn,
          writeWord_sparse_size, hn]; omega) (by omega),
      writeWordReadAbove _ _ _ _ _ (by
        rw [wordBytesArgsMemory_size _ _ _ _ _ hn, writeWord_sparse_size, hn]; omega)
        (by omega), wordBytesArgsMemory_read _ _ _ _ _ hn, hs]
  have hlen : contractSignatureCallLength signature.size = 4 + (96 + 32 * words.length) := by
    rw [contractSignatureCallLength, ABI.paddedSize, hn]
    omega
  rw [hlen, byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by omega)
      (by rw [hn] at *; omega), hsel, show ptr + 32 + 4 = ptr + 36 by omega, ht]
  simp only [contractSignatureCallBytes, ABI.paddedSize, hn, ByteArray.append_assoc]

def contractSignatureCallMemory (mem : ByteArray) (ptr len : Nat) (hash : UInt256)
    (words : List UInt256) : ByteArray :=
  contractSignatureEncodedMemory mem ptr len hash words

theorem contractSignatureCallMemory_size (mem : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32) :
    (contractSignatureCallMemory mem ptr len hash words).size =
      max mem.size (ptr + 164 + len) :=
  contractSignatureEncodedMemory_size mem ptr len hash words hn

theorem contractSignatureCallMemory_free (mem : ByteArray) (ptr len : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (contractSignatureCallMemory mem ptr len hash words) =
      UInt256.ofNat (contractSignatureCallEnd ptr len) :=
  contractSignatureEncodedMemory_free mem ptr len hash words hn hp

theorem contractSignatureCallMemory_preserved (mem : ByteArray) (ptr len off count : Nat)
    (hash : UInt256) (words : List UInt256) (hn : words.length = (len + 31) / 32)
    (hin : off + count ≤ mem.size) (hl : 96 ≤ off) (hh : off + count ≤ ptr) :
    (contractSignatureCallMemory mem ptr len hash words).readWithPadding off count =
      mem.readWithPadding off count :=
  contractSignatureEncodedMemory_preserved mem ptr len off count hash words hn hin hl hh

theorem contractSignatureCallMemory_read (mem : ByteArray) (ptr : Nat)
    (hash : UInt256) (signature : ByteArray) (words : List UInt256)
    (hn : words.length = (signature.size + 31) / 32) (hp : 96 ≤ ptr)
    (_hb : ptr + 32 < UInt256.size)
    (hs : (wordBytes words).extract 0 signature.size = signature) :
    (contractSignatureCallMemory mem ptr signature.size hash words).readWithPadding
      (ptr + 32) (contractSignatureCallLength signature.size) =
      contractSignatureCallBytes hash signature :=
  contractSignatureEncodedMemory_read mem ptr hash signature words hn hp hs

end Benchmarks.Safe.ViaIR
