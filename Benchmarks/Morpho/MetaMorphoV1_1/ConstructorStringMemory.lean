import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorArgumentWords
import Benchmarks.Morpho.MetaMorphoV1_1.StringEncoderBytePrefix
import Benchmarks.Morpho.MetaMorphoV1_1.BytesBuffer

/-! The constructor's string buffers and the memory preserved by their copies. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

-- LIBRARY CANDIDATE: read an arbitrary byte array between encoded prefixes and suffixes.
theorem encodedBytes_read (init rest : List UInt8) (bytes : ByteArray) :
    (init ++ bytes.toList ++ rest).toByteArray.readWithPadding init.length bytes.size =
      bytes := by
  by_cases hz : bytes.size = 0
  · rw [hz, byteArray_readWithPadding_zero]
    exact ByteArray.ext (Array.eq_empty_of_size_eq_zero hz).symm
  · rw [List.toByteArray_append, List.toByteArray_append, byteArray_toList_toByteArray,
      readWithPadding_eq_extract_unbounded _ _ _ (by omega)
        (by simp only [ByteArray.size_append, List.size_toByteArray]; omega),
      extract_append_left _ _ _ _ (by
        simp only [ByteArray.size_append, List.size_toByteArray]; omega),
      extract_append_right_window _ _ _ _ (by rw [List.size_toByteArray]),
      List.size_toByteArray, Nat.sub_self, Nat.add_sub_cancel_left, byteArray_extract_self]

namespace ConstructorArgs

theorem encoded_nameData (a : ConstructorArgs) :
    a.encoded.toByteArray.readWithPadding 224 a.name.size = a.name := by
  have h := encodedBytes_read
    (a.headWords.flatMap EVM.Word.toBytesBE ++ natBytes a.name.size)
    (zeroBytes (paddedSize a.name.size - a.name.size) ++
      natBytes a.symbol.size ++ padRightToWord a.symbol.toList) a.name
  have hl : (a.headWords.flatMap EVM.Word.toBytesBE ++ natBytes a.name.size).length =
      224 := by
    simp only [List.length_append, encodedWords_length, headWords,
      List.length_cons, List.length_nil, natBytes, word_toBytesBE_length_32]
  rw [hl] at h
  simpa only [encoded_head, padRightToWord, byteArray_toList_eq, Array.length_toList,
    List.append_assoc] using h

theorem encoded_symbolData (a : ConstructorArgs) :
    a.encoded.toByteArray.readWithPadding (256 + paddedSize a.name.size) a.symbol.size =
      a.symbol := by
  have h := encodedBytes_read
    (a.headWords.flatMap EVM.Word.toBytesBE ++ natBytes a.name.size ++
      padRightToWord a.name.toList ++ natBytes a.symbol.size)
    (zeroBytes (paddedSize a.symbol.size - a.symbol.size)) a.symbol
  have hl : (a.headWords.flatMap EVM.Word.toBytesBE ++ natBytes a.name.size ++
      padRightToWord a.name.toList ++ natBytes a.symbol.size).length =
      256 + paddedSize a.name.size := by
    simp only [List.length_append, encodedWords_length, headWords,
      List.length_cons, List.length_nil, natBytes, word_toBytesBE_length_32,
      abiPaddedBytes_length]
    omega
  rw [hl] at h
  simpa only [encoded_head, padRightToWord, byteArray_toList_eq, Array.length_toList,
    List.append_assoc] using h

end ConstructorArgs

theorem constructorArgumentMemory_read (a : ConstructorArgs) (off len : Nat)
    (hin : off + len ≤ a.encoded.length) :
    (constructorArgumentMemory a).readWithPadding (480 + off) len =
      a.encoded.toByteArray.readWithPadding off len := by
  by_cases hz : len = 0
  · simp only [hz, byteArray_readWithPadding_zero]
  · rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega)
        (by rw [constructorArgumentMemory_size]; omega),
      readWithPadding_eq_extract_unbounded _ _ _ (by omega)
        (by rw [List.size_toByteArray]; omega), constructorArgumentMemory_extract]

theorem constructorArgumentMemory_name (a : ConstructorArgs) :
    BytesBuffer (constructorArgumentMemory a) ⟨672⟩ a.name := by
  have hn : a.name.size ≤ paddedSize a.name.size := by unfold paddedSize; omega
  refine ⟨?_, ?_, ?_⟩
  · change 672 + 32 + a.name.size ≤ _
    rw [constructorArgumentMemory_size, a.encoded_length]; omega
  · apply loadedWord_of_read
    · change 672 + 32 ≤ _
      rw [constructorArgumentMemory_size, a.encoded_length]; omega
    · change (constructorArgumentMemory a).readWithPadding (480 + 192) 32 = _
      rw [constructorArgumentMemory_readWord a _ (by rw [a.encoded_length]; omega)]
      exact a.encoded_nameLength
  · change (constructorArgumentMemory a).readWithPadding (480 + 224) a.name.size = _
    rw [constructorArgumentMemory_read a _ _ (by rw [a.encoded_length]; omega)]
    exact a.encoded_nameData

theorem constructorArgumentMemory_symbol (a : ConstructorArgs)
    (hbound : 23666 + a.encoded.length < UInt256.size) :
    BytesBuffer (constructorArgumentMemory a)
      (UInt256.ofNat (704 + paddedSize a.name.size)) a.symbol := by
  have hs : a.symbol.size ≤ paddedSize a.symbol.size := by unfold paddedSize; omega
  have hp : 704 + paddedSize a.name.size < UInt256.size := by
    rw [a.encoded_length] at hbound; omega
  refine ⟨?_, ?_, ?_⟩
  · rw [UInt256.toNat_ofNat_of_lt hp, constructorArgumentMemory_size, a.encoded_length]
    omega
  · apply loadedWord_of_read
    · rw [UInt256.toNat_ofNat_of_lt hp, constructorArgumentMemory_size, a.encoded_length]
      omega
    · rw [UInt256.toNat_ofNat_of_lt hp]
      rw [show 704 + paddedSize a.name.size = 480 + (224 + paddedSize a.name.size) by omega,
        constructorArgumentMemory_readWord a _ (by rw [a.encoded_length]; omega)]
      exact a.encoded_symbolLength
  · rw [UInt256.toNat_ofNat_of_lt hp]
    have he : 704 + paddedSize a.name.size + 32 =
        480 + (256 + paddedSize a.name.size) := by omega
    rw [he, constructorArgumentMemory_read a _ _ (by rw [a.encoded_length]; omega)]
    exact a.encoded_symbolData

namespace SourceMemory

-- LIBRARY CANDIDATE: an aligned string reservation advances by its exact padded size.
theorem stringAllocationCursor (dest len : Nat) (hlen : len < 2 ^ 64) :
    nextCursor (UInt256.ofNat dest) (UInt256.ofNat (32 + paddedSize len)) =
      UInt256.ofNat (dest + 32 + paddedSize len) := by
  have hp : paddedSize len ≤ len + 31 := by unfold paddedSize; omega
  rw [nextCursor, roundedSize_aligned
    (by unfold paddedSize; omega)
    (by change 32 + paddedSize len + 31 < 2 ^ 256; omega), ofNat_add_words]
  congr 1
  omega

-- LIBRARY CANDIDATE: allocation of a padded string is a natural bound on its end cursor.
theorem stringAllocationFits (dest len : Nat) (hdest : dest < UInt256.size)
    (hlen : len < 2 ^ 64) :
    allocationFits (UInt256.ofNat dest) (UInt256.ofNat (32 + paddedSize len)) ↔
      dest + 32 + paddedSize len < 2 ^ 64 := by
  have hp : paddedSize len ≤ len + 31 := by unfold paddedSize; omega
  rw [allocationFits_iff_sum_lt, roundedSize_aligned
    (by unfold paddedSize; omega)
    (by change 32 + paddedSize len + 31 < 2 ^ 256; omega),
    UInt256.toNat_ofNat_of_lt hdest,
    UInt256.toNat_ofNat_of_lt (by change 32 + paddedSize len < 2 ^ 256; omega)]
  omega

-- LIBRARY CANDIDATE: the string payload copier materializes a buffer at its destination.
theorem stringPayloadMemory_buffer (mem bytes : ByteArray) (src dest : Nat)
    (hdest : dest < UInt256.size) (hlen : bytes.size < UInt256.size)
    (hin : src + bytes.size ≤ mem.size) (hbelow : src + bytes.size ≤ dest)
    (hread : mem.readWithPadding src bytes.size = bytes) :
    BytesBuffer (stringPayloadMemory mem src dest (UInt256.ofNat bytes.size))
      (UInt256.ofNat dest) bytes := by
  have hn := UInt256.toNat_ofNat_of_lt hlen
  have hi : src + (UInt256.ofNat bytes.size).toNat ≤ mem.size := by rwa [hn]
  refine ⟨?_, ?_, ?_⟩
  · rw [UInt256.toNat_ofNat_of_lt hdest, stringPayloadMemory_size _ _ _ _ hi, hn]
    omega
  · apply loadedWord_of_read
    · rw [UInt256.toNat_ofNat_of_lt hdest, stringPayloadMemory_size _ _ _ _ hi]
      omega
    · rw [UInt256.toNat_ofNat_of_lt hdest, stringPayloadMemory,
        writeWord_sparse_read_preserved _ _ _ _
          (.inl ⟨by omega, by rw [stringPayloadCopy_size _ _ _ _ hi]; omega⟩),
        stringPayloadCopy_word _ _ _ _ _ hi (by omega), writeWord_sparse_read_back]
  · have hc := stringPayloadCopy_read mem src dest (UInt256.ofNat bytes.size) hi
      (by rwa [hn])
    rw [hn] at hc
    rw [UInt256.toNat_ofNat_of_lt hdest, stringPayloadMemory,
      writeWord_sparse_read_preserved_unbounded _ _ _ _ _
        (by rw [stringPayloadCopy_size _ _ _ _ hi, hn]; omega) (.inl (by rw [hn])),
      hc, hread]

-- LIBRARY CANDIDATE: a string copy above the free-pointer slot preserves that slot.
theorem stringPayloadMemory_free (mem : ByteArray) (src dest : Nat) (len : UInt256)
    (hmem : 96 ≤ mem.size) (hin : src + len.toNat ≤ mem.size) (hlo : 96 ≤ dest) :
    memLoad ⟨64⟩ (stringPayloadMemory mem src dest len) = memLoad ⟨64⟩ mem := by
  have hr : (stringPayloadMemory mem src dest len).readWithPadding 64 32 =
      mem.readWithPadding 64 32 := by
    rw [stringPayloadMemory, writeWord_sparse_read_preserved _ _ _ _
      (.inl ⟨by omega, by rw [stringPayloadCopy_size _ _ _ _ hin]; omega⟩),
      stringPayloadCopy_word _ _ _ _ _ hin (by omega),
      writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨hlo, hmem⟩)]
  simp only [memLoad, show (⟨64⟩ : UInt256).toNat = 64 from rfl,
    if_neg (show ¬64 ≥ (stringPayloadMemory mem src dest len).size by
      rw [stringPayloadMemory_size _ _ _ _ hin]; omega), if_neg (show ¬64 ≥ mem.size by omega), hr]

end SourceMemory

end Benchmarks.Morpho.MetaMorphoV1_1
