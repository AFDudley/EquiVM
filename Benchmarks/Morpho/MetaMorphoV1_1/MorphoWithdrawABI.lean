import Benchmarks.Morpho.MetaMorphoV1_1.MorphoSupplyABI

/-! Morpho withdrawal calldata and its two unrestricted return words. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def morphoWithdrawSelector : ByteArray := ⟨#[0x5c, 0x2b, 0xea, 0x49]⟩
def morphoWithdrawSelectorWord : UInt256 := UInt256.shiftLeft ⟨1546381897⟩ ⟨224⟩

def morphoWithdrawWords (p : MarketParamsData) (assets shares : UInt256)
    (owner receiver : AccountAddress) : List UInt256 :=
  p.words ++ [assets, shares, UInt256.ofNat owner.toNat, UInt256.ofNat receiver.toNat]

def morphoWithdrawCalldata (p : MarketParamsData) (assets shares : UInt256)
    (owner receiver : AccountAddress) : ByteArray :=
  morphoWithdrawSelector ++ wordBytes (morphoWithdrawWords p assets shares owner receiver)

theorem morphoWithdrawCalldata_size (p : MarketParamsData) (assets shares : UInt256)
    (owner receiver : AccountAddress) :
    (morphoWithdrawCalldata p assets shares owner receiver).size = 292 := by
  simp only [morphoWithdrawCalldata, ByteArray.size_append, wordBytes_size, morphoWithdrawWords,
    List.length_append, MarketParamsData.words, List.length_cons, List.length_nil]
  rfl

theorem morphoWithdrawEncode (p : MarketParamsData) (assets shares : UInt256)
    (owner receiver : AccountAddress) :
    config.externalABI.encode? "withdraw"
      [p.value, uint256Value assets, uint256Value shares, .address owner, .address receiver] =
      some (morphoWithdrawCalldata p assets shares owner receiver) := by
  change encodeCallWithSelector?
    (ByteArray.mk ((EVM.Word.ofNat 0x5c2bea49).toBytesBE.drop 28).toArray)
    [.tuple marketParamsTypes, abiUInt256, abiUInt256, abiAddress, abiAddress]
    [.tuple (rateParamsFields p), uint256Value assets, uint256Value shares,
      .address owner, .address receiver] = _
  rw [show ByteArray.mk ((EVM.Word.ofNat 0x5c2bea49).toBytesBE.drop 28).toArray =
    morphoWithdrawSelector from by decide +kernel]
  have hh : abiTupleHeadSize? [.tuple marketParamsTypes, abiUInt256, abiUInt256, abiAddress,
      abiAddress] = some 288 := by
    simp [marketParamsTypes, abiTupleHeadSize?, isDynamicABIType, isDynamicABITypeList,
      staticABIEncodedSize?, staticABIEncodedSizeList?, abiAddress, abiUInt256]
  rw [encodeCallWithSelector?, encodeABIValues?, hh]
  simp only [encodeABIValuesFrom?, marketParamsTupleEncode, encodeABIValue_uint256_word,
    encodeAddressWord, show isDynamicABIType (.tuple marketParamsTypes) = false from rfl,
    show isDynamicABIType abiUInt256 = false from rfl,
    show isDynamicABIType abiAddress = false from rfl,
    bind, Option.bind, Bool.false_eq_true, if_false, List.nil_append, List.append_nil,
    morphoWithdrawCalldata, morphoWithdrawWords, wordBytes_append, wordBytes,
    MarketParamsData.bytes, byteArray_toList_append, ByteArray.append_empty]
  rw [← byteArray_toList_append, ← byteArray_toList_append, ← byteArray_toList_append,
    ← byteArray_toList_append, byteArray_toList_toByteArray]
  simp only [ByteArray.append_assoc]

theorem morphoWithdrawDecode {out : ByteArray} (hhi : out.size < 2 ^ 255) :
    config.externalABI.decode? "withdraw" out =
      if 64 ≤ out.size then
        some [uint256Value (calldataWord out 0), uint256Value (calldataWord out 32)] else none := by
  change (decodeReturnValues? [abiUInt256, abiUInt256] out).bind some = _
  rw [uint256PairReturnDecode hhi]
  split <;> rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
