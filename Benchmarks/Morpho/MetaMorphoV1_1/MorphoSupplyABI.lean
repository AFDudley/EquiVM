import Benchmarks.Morpho.MetaMorphoV1_1.BorrowRateABI

/-! Morpho supply calldata with empty callback data, and its two-word return value. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def morphoSupplySelector : ByteArray := ⟨#[0xa9, 0x9a, 0xad, 0x89]⟩

def morphoSupplySelectorWord : UInt256 := UInt256.shiftLeft ⟨2845486473⟩ ⟨224⟩

def morphoSupplyWords (p : MarketParamsData) (amount : UInt256) (sender : AccountAddress) :
    List UInt256 := p.words ++ [amount, ⟨0⟩, UInt256.ofNat sender.toNat, ⟨288⟩, ⟨0⟩]

def morphoSupplyCalldata (p : MarketParamsData) (amount : UInt256) (sender : AccountAddress) :
    ByteArray := morphoSupplySelector ++ wordBytes (morphoSupplyWords p amount sender)

theorem morphoSupplyCalldata_size (p : MarketParamsData) (amount : UInt256)
    (sender : AccountAddress) : (morphoSupplyCalldata p amount sender).size = 324 := by
  simp only [morphoSupplyCalldata, ByteArray.size_append, wordBytes_size, morphoSupplyWords,
    List.length_append, MarketParamsData.words, List.length_cons, List.length_nil]
  rfl

theorem morphoSupplyEncode (p : MarketParamsData) (amount : UInt256) (sender : AccountAddress) :
    config.externalABI.encode? "supply"
      [p.value, uint256Value amount, uint256Value ⟨0⟩, .address sender, .bytes ByteArray.empty] =
      some (morphoSupplyCalldata p amount sender) := by
  change encodeCallWithSelector?
    (ByteArray.mk ((EVM.Word.ofNat 0xa99aad89).toBytesBE.drop 28).toArray)
    [.tuple marketParamsTypes, abiUInt256, abiUInt256, abiAddress, .bytes]
    [.tuple (rateParamsFields p), uint256Value amount, uint256Value ⟨0⟩,
      .address sender, .bytes ByteArray.empty] = _
  rw [show ByteArray.mk ((EVM.Word.ofNat 0xa99aad89).toBytesBE.drop 28).toArray =
    morphoSupplySelector from by decide +kernel]
  have hh : abiTupleHeadSize? [.tuple marketParamsTypes, abiUInt256, abiUInt256, abiAddress,
      .bytes] = some 288 := by
    simp [marketParamsTypes, abiTupleHeadSize?, isDynamicABIType, isDynamicABITypeList,
      staticABIEncodedSize?, staticABIEncodedSizeList?, abiAddress, abiUInt256]
  have hb : encodeABIValue? .bytes (.bytes ByteArray.empty) =
      some (⟨0⟩ : UInt256).toByteArray.toList := by
    rw [encodeABIValue?]
    decide +kernel
  rw [encodeCallWithSelector?, encodeABIValues?, hh]
  simp only [encodeABIValuesFrom?, marketParamsTupleEncode, encodeABIValue_uint256_word,
    encodeAddressWord, hb, show isDynamicABIType (.tuple marketParamsTypes) = false from rfl,
    show isDynamicABIType abiUInt256 = false from rfl,
    show isDynamicABIType abiAddress = false from rfl,
    show isDynamicABIType .bytes = true from rfl,
    bind, Option.bind, Bool.false_eq_true, Bool.true_eq, if_false, if_true,
    List.nil_append, List.append_nil, List.length_nil, Nat.add_zero, natBytes,
    EVM.Word.ofNat, word_toBytesBE_eq_toByteArray_toList, List.append_assoc,
    morphoSupplyCalldata, morphoSupplyWords, wordBytes_append, wordBytes,
    MarketParamsData.bytes, byteArray_toList_append, ByteArray.append_empty,
    uint256Value]
  rw [← byteArray_toList_append, ← byteArray_toList_append, ← byteArray_toList_append,
    ← byteArray_toList_append, ← byteArray_toList_append, byteArray_toList_toByteArray]
  rfl

-- LIBRARY CANDIDATE: the modern return decoder for two unrestricted unsigned words.
theorem uint256PairReturnDecode {out : ByteArray} (hhi : out.size < 2 ^ 255) :
    decodeReturnValues? [abiUInt256, abiUInt256] out =
      if 64 ≤ out.size then
        some [uint256Value (calldataWord out 0), uint256Value (calldataWord out 32)] else none := by
  rw [decodeReturnValues_scalarWords_eq (by decide)]
  rw [if_neg (by
    rintro ⟨_, hhuge⟩
    rw [byteArray_toList_eq, Array.length_toList] at hhuge
    exact Nat.not_le_of_gt hhi hhuge)]
  by_cases hl : 64 ≤ out.size
  · rw [if_pos hl]
    have hw0 := (calldataWord out 0).val.isLt
    have hw32 := (calldataWord out 32).val.isLt
    simp only [decodeScalarWords?, abiUInt256,
      decodeScalarUint_at (out := out) (off := 0) ⟨256, by decide⟩ (by decide) (by omega),
      Nat.reduceAdd,
      decodeScalarUint_at (out := out) (off := 32) ⟨256, by decide⟩ (by decide) (by omega),
      show (calldataWord out 0).toNat < 2 ^ 256 from hw0,
      show (calldataWord out 32).toNat < 2 ^ 256 from hw32,
      if_true, bind, Option.bind]
  · rw [if_neg hl]
    cases h : decodeScalarWords? [abiUInt256, abiUInt256] out.toList 0 with
    | none => rfl
    | some vs =>
        have hlen := decodeScalarWords?_some_length (by omega) h
        simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
          Nat.zero_add, byteArray_toList_eq, Array.length_toList] at hlen
        change 64 ≤ out.size at hlen
        omega

theorem morphoSupplyDecode {out : ByteArray} (hhi : out.size < 2 ^ 255) :
    config.externalABI.decode? "supply" out =
      if 64 ≤ out.size then
        some [uint256Value (calldataWord out 0), uint256Value (calldataWord out 32)] else none := by
  change (decodeReturnValues? [abiUInt256, abiUInt256] out).bind some = _
  rw [uint256PairReturnDecode hhi]
  split <;> rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
