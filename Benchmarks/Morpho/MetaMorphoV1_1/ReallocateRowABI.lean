import Benchmarks.Morpho.MetaMorphoV1_1.CalldataWordWindow
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateCalldata
import Benchmarks.Morpho.MetaMorphoV1_1.SubmitCapCalldata

/-! A reallocation row contains five market words followed by its target asset amount. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def reallocateRowBytes (cd : ByteArray) (start : Nat) : ByteArray :=
  cd.extract start (start + 192)

def reallocateRowValue (row : ByteArray) : Value :=
  .tuple [.tuple (marketParamsFields row), uint256Value (calldataWord row 160)]

theorem reallocateRowBytes_list (cd : ByteArray) (start : Nat) :
    (reallocateRowBytes cd start).toList = (cd.toList.drop start).take 192 := by
  rw [reallocateRowBytes, extract_toList, Nat.add_sub_cancel_left]

theorem reallocateRowBytes_size {cd : ByteArray} {start : Nat}
    (hin : start + 192 ≤ cd.size) : (reallocateRowBytes cd start).size = 192 := by
  simp only [reallocateRowBytes, ByteArray.size_extract]
  omega

theorem reallocateRowBytes_word {cd : ByteArray} {start off : Nat}
    (hin : start + 192 ≤ cd.size) (hoff : off + 32 ≤ 192) :
    calldataWord (reallocateRowBytes cd start) off = calldataWord cd (start + off) := by
  have hw : bytesToWord (((reallocateRowBytes cd start).toList.drop off).take 32) =
      calldataWord (reallocateRowBytes cd start) off :=
    decode_word_at_eq_any _ off (by rw [reallocateRowBytes_size hin]; omega)
  rw [← hw, reallocateRowBytes_list, List.drop_take, List.drop_drop, List.take_take,
    Nat.min_eq_left (by omega)]
  exact decode_word_at_eq_any cd (start + off) (by omega)

set_option maxRecDepth 2000 in
theorem reallocateRowABIDecode {row : ByteArray} (hrow : 192 ≤ row.size) :
    decodeABIValue? reallocateItemType row.toList 0 =
      if MarketParamsChecks row then some (reallocateRowValue row, 192) else none := by
  have htuple : decodeABIValue? (.tuple marketParamsFieldTypes) row.toList 0 =
      (decodeScalarWords? marketParamsFieldTypes row.toList 0).map
        (fun vs ↦ (.tuple vs, 160)) := scalarTupleValueDecode (by decide)
  have hu : decodeABIValue? abiUInt256 row.toList 160 =
      some (uint256Value (calldataWord row 160), 192) := by
    have hl : ((row.toList.drop 160).take 32).length = 32 := by
      simp only [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
      change min 32 (row.size - 160) = 32
      omega
    simpa only [decode_word_at_eq_any row 160 (by omega)] using decodeABIValue_uint256_ok hl
  change decodeABIValue? (.tuple [.tuple marketParamsFieldTypes, abiUInt256]) row.toList 0 = _
  rw [decodeABIValue?, submitCapCalldataHeadSize]
  simp only [bind, Option.bind, Nat.zero_add]
  rw [decodeABIValues?]
  simp only [show isDynamicABIType (.tuple marketParamsFieldTypes) = false from rfl,
    show staticABIEncodedSize? (.tuple marketParamsFieldTypes) = some 160 from rfl,
    Bool.false_eq_true, if_false, bind, Option.bind, Nat.zero_add, htuple,
    marketParamsScalarDecode_long (by omega : 160 ≤ row.size)]
  by_cases hc : MarketParamsChecks row <;>
    simp [hc, decodeABIValues?, hu, show isDynamicABIType abiUInt256 = false from rfl,
      show staticABIEncodedSize? abiUInt256 = some 32 from rfl, reallocateRowValue]

set_option maxRecDepth 2000 in
theorem reallocateRowDecodeValue {cd : ByteArray} {start : Nat} (plan : CalldataPlan)
    (hstart : 4 ≤ start) (hin : start + 192 ≤ cd.size) (hhi : cd.size < 2 ^ 255 + 4) :
    decodeValue? reallocateItemType cd.toList start plan false =
      if MarketParamsChecks (reallocateRowBytes cd start) then
        some (reallocateRowValue (reallocateRowBytes cd start)) else none := by
  have hsize : cd.size < UInt256.size := by change _ < 2 ^ 256; omega
  have hstartword : start < UInt256.size := by omega
  have hl : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hsub : solcSub cd.size start = cd.size - start := by
    change (UInt256.ofNat cd.size - UInt256.ofNat start).toNat = _
    exact usub_ofNat_lit_toNat (by omega) hsize
  have hcheck : solcSLT (solcSub cd.size start) 192 = false := by
    have h := (solcSLT_word_false (UInt256.ofNat (cd.size - start)) ⟨192⟩).mpr
      (slt_ofNat_lit_zero (n := cd.size - start) (m := 192) (by decide) (by omega) (by omega))
    rw [UInt256.toNat_ofNat_of_lt (by omega : cd.size - start < UInt256.size)] at h
    simpa only [hsub] using h
  have hwords : solcReadWords cd.toList start 6 = (reallocateRowBytes cd start).toList := by
    rw [reallocateRowBytes_list]
    exact solcReadWords_bounded (by change start + 32 * 6 < 2 ^ 256; omega) (by rw [hl]; omega)
  change decodeValue? (.tuple [.tuple marketParamsFieldTypes, abiUInt256])
    cd.toList start plan false = _
  rw [decodeValue?, submitCapCalldataHeadSize]
  simp only [bind, Option.bind, Bool.not_false, Bool.true_or, hl, hcheck,
    Bool.and_false, Bool.false_eq_true, if_false,
    show isDynamicABIType (.tuple [.tuple marketParamsFieldTypes, abiUInt256]) = false from rfl,
    Bool.not_false, if_true, show 192 / 32 = 6 from rfl, hwords]
  rw [show (.tuple [.tuple marketParamsFieldTypes, abiUInt256]) = reallocateItemType from rfl,
    reallocateRowABIDecode (by rw [reallocateRowBytes_size hin])]
  split_ifs <;> rfl

theorem retainedReallocateRow {cd : ByteArray} {base i : Nat}
    (hbase : 4 ≤ base) (hin : base + 192 * i + 192 ≤ cd.size)
    (hhi : cd.size < 2 ^ 255 + 4) :
    retainedCalldataElement reallocateItemType reallocateCalldataPlan cd.toList base 192 i =
      if MarketParamsChecks (reallocateRowBytes cd (base + 192 * i)) then
        reallocateRowValue (reallocateRowBytes cd (base + 192 * i)) else decodeFailure := by
  have hword : base + 192 * i < EVM.wordModulus := by change _ < 2 ^ 256; omega
  simp only [retainedCalldataElement, show isDynamicABIType reallocateItemType = false from rfl,
    Bool.false_eq_true, if_false, Bool.false_and, bind, Option.bind_some,
    solcAdd, Nat.mod_eq_of_lt hword]
  rw [reallocateRowDecodeValue _ (by omega) hin hhi]
  split_ifs <;> rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
