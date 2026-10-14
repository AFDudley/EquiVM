import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStringMemory

/-! Allocated name and symbol buffers used throughout the constructor body. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

namespace SourceMemory

-- LIBRARY CANDIDATE: allocate and copy a length-prefixed memory buffer.
def allocatedStringMemory (mem : ByteArray) (src dest : Nat) (bytes : ByteArray) : ByteArray :=
  stringPayloadMemory (writeWord mem 64 (UInt256.ofNat (dest + 32 + paddedSize bytes.size)))
    (src + 32) dest (UInt256.ofNat bytes.size)

theorem allocatedStringMemory_prefix (mem : ByteArray) (src dest : Nat) (bytes : ByteArray)
    (hlen : bytes.size < UInt256.size) (hin : src + 32 + bytes.size ≤ mem.size) :
    ByteMemoryPrefix mem (allocatedStringMemory mem src dest bytes) dest := by
  exact (byteMemoryPrefix_writeWord mem 64 dest _ (.inr (by decide))).trans
    (stringPayloadMemory_bytePrefix _ _ _ _ (by
      rw [UInt256.toNat_ofNat_of_lt hlen, writeWord_sparse_size]; omega))

theorem allocatedStringMemory_buffer (mem : ByteArray) (src dest : Nat) (bytes : ByteArray)
    (hsrc : src < UInt256.size) (hdest : dest < UInt256.size)
    (hlen : bytes.size < UInt256.size) (hlo : 96 ≤ src)
    (hbelow : src + 32 + bytes.size ≤ dest)
    (hbuf : BytesBuffer mem (UInt256.ofNat src) bytes) :
    BytesBuffer (allocatedStringMemory mem src dest bytes) (UInt256.ofNat dest) bytes := by
  have hh := hbuf.writeWord 64 (UInt256.ofNat (dest + 32 + paddedSize bytes.size))
    (.inr (by rw [UInt256.toNat_ofNat_of_lt hsrc]; omega))
  have hs := hh.size
  have hr := hh.data
  rw [UInt256.toNat_ofNat_of_lt hsrc] at hs hr
  exact stringPayloadMemory_buffer _ bytes (src + 32) dest hdest hlen hs hbelow hr

theorem allocatedStringMemory_free (mem : ByteArray) (src dest : Nat) (bytes : ByteArray)
    (hlen : bytes.size < UInt256.size) (hin : src + 32 + bytes.size ≤ mem.size)
    (hlo : 96 ≤ dest) :
    memLoad ⟨64⟩ (allocatedStringMemory mem src dest bytes) =
      UInt256.ofNat (dest + 32 + paddedSize bytes.size) := by
  rw [allocatedStringMemory, stringPayloadMemory_free _ _ _ _
    (by rw [writeWord_sparse_size]; omega)
    (by rw [UInt256.toNat_ofNat_of_lt hlen, writeWord_sparse_size]; omega) hlo]
  exact memLoad_write_same mem 64 ⟨64⟩ _ rfl

end SourceMemory

namespace ConstructorArgs

def argumentEnd (a : ConstructorArgs) : Nat := 480 + a.encoded.length
def nameEnd (a : ConstructorArgs) : Nat := a.argumentEnd + 32 + paddedSize a.name.size
def stringsEnd (a : ConstructorArgs) : Nat := a.nameEnd + 32 + paddedSize a.symbol.size

theorem string_sizes_small (a : ConstructorArgs) (hsmall : a.argumentEnd < 2 ^ 64) :
    a.name.size < 2 ^ 64 ∧ a.symbol.size < 2 ^ 64 := by
  have hn : a.name.size ≤ paddedSize a.name.size := by unfold paddedSize; omega
  have hs : a.symbol.size ≤ paddedSize a.symbol.size := by unfold paddedSize; omega
  rw [argumentEnd, a.encoded_length] at hsmall
  omega

end ConstructorArgs

def constructorNameMemory (a : ConstructorArgs) : ByteArray :=
  allocatedStringMemory (constructorArgumentMemory a) 672 a.argumentEnd a.name

def constructorStringsMemory (a : ConstructorArgs) : ByteArray :=
  allocatedStringMemory (constructorNameMemory a)
    (704 + paddedSize a.name.size) a.nameEnd a.symbol

theorem constructorNameMemory_prefix (a : ConstructorArgs)
    (hsmall : a.argumentEnd < 2 ^ 64) :
    ByteMemoryPrefix (constructorArgumentMemory a) (constructorNameMemory a) a.argumentEnd := by
  exact allocatedStringMemory_prefix _ _ _ _ (by
    have := (a.string_sizes_small hsmall).1; change _ < 2 ^ 256; omega)
    (constructorArgumentMemory_name a).size

theorem constructorNameMemory_free (a : ConstructorArgs)
    (hsmall : a.argumentEnd < 2 ^ 64) :
    memLoad ⟨64⟩ (constructorNameMemory a) = UInt256.ofNat a.nameEnd := by
  exact allocatedStringMemory_free _ _ _ _ (by
    have := (a.string_sizes_small hsmall).1; change _ < 2 ^ 256; omega)
    (constructorArgumentMemory_name a).size (by unfold ConstructorArgs.argumentEnd; omega)

theorem constructorNameMemory_name (a : ConstructorArgs)
    (hsmall : a.argumentEnd < 2 ^ 64) :
    BytesBuffer (constructorNameMemory a) (UInt256.ofNat a.argumentEnd) a.name := by
  apply allocatedStringMemory_buffer _ _ _ _ (by decide)
    (by change a.argumentEnd < 2 ^ 256; omega)
    (by have := (a.string_sizes_small hsmall).1; change _ < 2 ^ 256; omega) (by decide)
  · have h := (constructorArgumentMemory_name a).size
    rwa [constructorArgumentMemory_size] at h
  · exact constructorArgumentMemory_name a

theorem constructorNameMemory_symbol (a : ConstructorArgs)
    (hbound : 23666 + a.encoded.length < UInt256.size) (hsmall : a.argumentEnd < 2 ^ 64) :
    BytesBuffer (constructorNameMemory a)
      (UInt256.ofNat (704 + paddedSize a.name.size)) a.symbol := by
  have hp : 704 + paddedSize a.name.size < UInt256.size := by
    rw [a.encoded_length] at hbound; omega
  apply (constructorArgumentMemory_symbol a hbound).preserve
    (constructorNameMemory_prefix a hsmall)
  · rw [UInt256.toNat_ofNat_of_lt hp]; omega
  · have h := (constructorArgumentMemory_symbol a hbound).size
    rwa [constructorArgumentMemory_size] at h

theorem constructorStringsMemory_prefix (a : ConstructorArgs)
    (hbound : 23666 + a.encoded.length < UInt256.size) (hsmall : a.argumentEnd < 2 ^ 64) :
    ByteMemoryPrefix (constructorNameMemory a) (constructorStringsMemory a) a.nameEnd := by
  have hp : 704 + paddedSize a.name.size < UInt256.size := by
    rw [a.encoded_length] at hbound; omega
  apply allocatedStringMemory_prefix _ _ _ _ (by
    have := (a.string_sizes_small hsmall).2; change _ < 2 ^ 256; omega)
  have h := (constructorNameMemory_symbol a hbound hsmall).size
  rwa [UInt256.toNat_ofNat_of_lt hp] at h

theorem constructorStringsMemory_free (a : ConstructorArgs)
    (hbound : 23666 + a.encoded.length < UInt256.size) (hsmall : a.argumentEnd < 2 ^ 64) :
    memLoad ⟨64⟩ (constructorStringsMemory a) = UInt256.ofNat a.stringsEnd := by
  have hp : 704 + paddedSize a.name.size < UInt256.size := by
    rw [a.encoded_length] at hbound; omega
  apply allocatedStringMemory_free _ _ _ _ (by
    have := (a.string_sizes_small hsmall).2; change _ < 2 ^ 256; omega)
  · have h := (constructorNameMemory_symbol a hbound hsmall).size
    rwa [UInt256.toNat_ofNat_of_lt hp] at h
  · unfold ConstructorArgs.nameEnd ConstructorArgs.argumentEnd; omega

theorem constructorStringsMemory_name (a : ConstructorArgs)
    (hbound : 23666 + a.encoded.length < UInt256.size) (hsmall : a.argumentEnd < 2 ^ 64) :
    BytesBuffer (constructorStringsMemory a) (UInt256.ofNat a.argumentEnd) a.name := by
  apply (constructorNameMemory_name a hsmall).preserve
    (constructorStringsMemory_prefix a hbound hsmall)
  · rw [UInt256.toNat_ofNat_of_lt (by change a.argumentEnd < 2 ^ 256; omega)]
    unfold ConstructorArgs.argumentEnd; omega
  · rw [UInt256.toNat_ofNat_of_lt (by change a.argumentEnd < 2 ^ 256; omega)]
    have : a.name.size ≤ paddedSize a.name.size := by unfold paddedSize; omega
    unfold ConstructorArgs.nameEnd; omega

theorem constructorStringsMemory_symbol (a : ConstructorArgs)
    (hbound : 23666 + a.encoded.length < UInt256.size) (hsmall : a.argumentEnd < 2 ^ 64)
    (hname : a.nameEnd < 2 ^ 64) :
    BytesBuffer (constructorStringsMemory a) (UInt256.ofNat a.nameEnd) a.symbol := by
  apply allocatedStringMemory_buffer _ _ _ _
    (by rw [a.encoded_length] at hbound; omega)
    (by change a.nameEnd < 2 ^ 256; omega)
    (by have := (a.string_sizes_small hsmall).2; change _ < 2 ^ 256; omega) (by omega)
  · have h := (constructorArgumentMemory_symbol a hbound).size
    rw [UInt256.toNat_ofNat_of_lt (by rw [a.encoded_length] at hbound; omega),
      constructorArgumentMemory_size] at h
    unfold ConstructorArgs.nameEnd ConstructorArgs.argumentEnd; omega
  · exact constructorNameMemory_symbol a hbound hsmall

end Benchmarks.Morpho.MetaMorphoV1_1
