import Benchmarks.Morpho.MetaMorphoV1_1.BorrowRateABI

/-! ABI encoding of Morpho's state-changing interest-accrual call. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def morphoAccrueSelector : ByteArray := ⟨#[0x15, 0x1c, 0x1a, 0xde]⟩

def morphoAccrueSelectorWord : UInt256 := UInt256.shiftLeft ⟨177081711⟩ ⟨225⟩

def morphoAccrueCalldata (p : MarketParamsData) : ByteArray :=
  morphoAccrueSelector ++ p.bytes

theorem morphoAccrueCalldata_size (p : MarketParamsData) :
    (morphoAccrueCalldata p).size = 164 := by
  simp only [morphoAccrueCalldata, ByteArray.size_append, MarketParamsData.bytes,
    wordBytes_size, MarketParamsData.words, List.length_cons, List.length_nil]
  rfl

theorem morphoAccrueEncode (p : MarketParamsData) :
    config.externalABI.encode? "accrueInterest" [p.value] =
      some (morphoAccrueCalldata p) := by
  change encodeCallWithSelector?
    (ByteArray.mk ((EVM.Word.ofNat 0x151c1ade).toBytesBE.drop 28).toArray)
    [.tuple marketParamsTypes] [.tuple (rateParamsFields p)] = _
  rw [show ByteArray.mk ((EVM.Word.ofNat 0x151c1ade).toBytesBE.drop 28).toArray =
    morphoAccrueSelector from by decide +kernel]
  have hh : abiTupleHeadSize? [.tuple marketParamsTypes] = some 160 := by
    simp [marketParamsTypes, abiTupleHeadSize?, isDynamicABIType, isDynamicABITypeList,
      staticABIEncodedSize?, staticABIEncodedSizeList?, abiAddress, abiUInt256]
  rw [encodeCallWithSelector?, encodeABIValues?, hh]
  simp only [encodeABIValuesFrom?, marketParamsTupleEncode,
    show isDynamicABIType (.tuple marketParamsTypes) = false from rfl,
    bind, Option.bind, Bool.false_eq_true, if_false, List.nil_append, List.append_nil,
    morphoAccrueCalldata]
  rw [byteArray_toList_toByteArray]

theorem morphoAccrueDecode (out : ByteArray) :
    config.externalABI.decode? "accrueInterest" out = some [] := rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
