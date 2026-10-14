import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateABI
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateLoopData
import Benchmarks.Morpho.MetaMorphoV1_1.BytesArrayDecode

/-! The bounds accepted by the compiler's 192-byte allocation-array decoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def reallocateCount (cd : ByteArray) : UInt256 := calldataWord cd (reallocateArrayHead cd).toNat

structure ReallocateCalldataChecks (cd : ByteArray) : Prop where
  head : 36 ≤ cd.size
  high : cd.size < 2 ^ 255
  offset : (calldataWord cd 4).toNat ≤ solcMaxU64
  length : (reallocateCount cd).toNat ≤ solcMaxU64
  extent : (calldataWord cd 4).toNat + 36 + 192 * (reallocateCount cd).toNat ≤ cd.size

theorem reallocateArrayHead_toNat {cd : ByteArray}
    (ho : (calldataWord cd 4).toNat ≤ solcMaxU64) :
    (reallocateArrayHead cd).toNat = 4 + (calldataWord cd 4).toNat := add4_word_toNat _ ho

theorem reallocateHeaderWordCheck {cd : ByteArray}
    (ho : (calldataWord cd 4).toNat ≤ solcMaxU64) (hs : cd.size < UInt256.size) :
    (UInt256.slt (calldataWord cd 4 + UInt256.ofNat 35) (UInt256.ofNat cd.size) ≠ ⟨0⟩) ↔
      cd.size < 2 ^ 255 ∧ (calldataWord cd 4).toNat + 36 ≤ cd.size := by
  have ho' : (calldataWord cd 4).toNat ≤ 2 ^ 64 - 1 := ho
  have ha : (calldataWord cd 4 + UInt256.ofNat 35).toNat = (calldataWord cd 4).toNat + 35 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2 ^ 256; omega)
  by_cases hhigh : cd.size < 2 ^ 255
  · by_cases hbound : (calldataWord cd 4).toNat + 36 ≤ cd.size
    · rw [slt_lit_one_low hhigh (by rw [ha]; omega)]
      simp only [hhigh, hbound, and_self]
      decide
    · rw [slt_lit_zero hhigh (by rw [ha]; omega) (by rw [ha]; omega)]
      simp only [ne_eq, not_true_eq_false, hbound, and_false]
  · rw [slt_zero_low_high (by rw [ha]; omega)
      (by rw [UInt256.toNat_ofNat_of_lt hs]; omega)]
    simp only [ne_eq, not_true_eq_false, hhigh, false_and]

theorem reallocateExtent_toNat (offset len : UInt256)
    (ho : offset.toNat ≤ solcMaxU64) (hl : len.toNat ≤ solcMaxU64) :
    ((offset + UInt256.mul len (UInt256.ofNat 192)) + UInt256.ofNat 36).toNat =
      offset.toNat + 36 + 192 * len.toNat := by
  have ho' : offset.toNat ≤ 2 ^ 64 - 1 := ho
  have hl' : len.toNat ≤ 2 ^ 64 - 1 := hl
  have hm : (UInt256.mul len (UInt256.ofNat 192)).toNat = len.toNat * 192 :=
    umul_toNat _ _ (by change len.toNat * 192 < 2 ^ 256; omega)
  have ha : (offset + UInt256.mul len (UInt256.ofNat 192)).toNat = offset.toNat + len.toNat * 192 := by
    rw [uadd_toNat, hm, Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)]
  rw [uadd_word_ofNat_toNat _ _ (by rw [ha]; change _ < 2 ^ 256; omega), ha]
  omega

set_option maxRecDepth 2000 in
theorem reallocateBadExtentChecks {cd : ByteArray}
    (ho : (calldataWord cd 4).toNat ≤ solcMaxU64)
    (hl : (reallocateCount cd).toNat ≤ solcMaxU64) (hs : cd.size < UInt256.size) :
    badExtent false false cd.toList (reallocateArrayHead cd).toNat (reallocateCount cd).toNat 192 = false ↔
      cd.size < 2 ^ 255 ∧ (calldataWord cd 4).toNat + 36 + 192 * (reallocateCount cd).toNat ≤ cd.size := by
  have ho' : (calldataWord cd 4).toNat ≤ 2 ^ 64 - 1 := ho
  have hl' : (reallocateCount cd).toNat ≤ 2 ^ 64 - 1 := hl
  have hh := reallocateArrayHead_toNat ho
  have hbytes : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have h31 : solcAdd (reallocateArrayHead cd).toNat 31 = (calldataWord cd 4).toNat + 35 := by
    rw [solcAdd, hh, Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)]
    omega
  have hend : solcAdd (solcAdd (reallocateArrayHead cd).toNat 32) ((reallocateCount cd).toNat * 192) =
      (calldataWord cd 4).toNat + 36 + 192 * (reallocateCount cd).toNat := by
    have h32 : solcAdd (reallocateArrayHead cd).toNat 32 = 4 + (calldataWord cd 4).toNat + 32 := by
      rw [solcAdd, hh, Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)]
    rw [h32, solcAdd, Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)]
    omega
  have hsl : solcSLT ((calldataWord cd 4).toNat + 35) cd.size = true ↔
      cd.size < 2 ^ 255 ∧ (calldataWord cd 4).toNat + 36 ≤ cd.size := by
    have ha : (calldataWord cd 4 + UInt256.ofNat 35).toNat = (calldataWord cd 4).toNat + 35 :=
      uadd_word_ofNat_toNat _ _ (by change _ < 2 ^ 256; omega)
    have he := solcSLT_word_false (calldataWord cd 4 + UInt256.ofNat 35) (UInt256.ofNat cd.size)
    rw [ha, UInt256.toNat_ofNat_of_lt hs] at he
    rw [← reallocateHeaderWordCheck ho hs]
    constructor
    · intro h hz
      rw [he.mpr hz] at h
      cases h
    · intro h
      exact Bool.eq_true_of_not_eq_false (fun hf ↦ h (he.mp hf))
  simp only [badExtent, Bool.not_false, Bool.true_and, Bool.false_and, Bool.false_eq_true,
    if_false, hbytes, h31, hend, Nat.mod_eq_of_lt (show cd.size < EVM.wordModulus from hs), Bool.or_eq_false_iff,
    Bool.not_eq_false', decide_eq_false_iff_not, Nat.not_lt]
  rw [hsl]
  constructor <;> rintro h
  · exact ⟨h.1.1, h.2⟩
  · exact ⟨⟨h.1, by omega⟩, h.2⟩

open Classical in
set_option maxRecDepth 2000 in
theorem reallocateDecodeChecks {I : ExecutionEnv}
    (hsel : selIs I (metaMorphoV1_1SelBytes 34)) (hsize : I.calldata.size < UInt256.size) :
    config.externalABI.decodeCalldata? (reallocateTransition.params.map (·.name))
        (reallocateTransition.params.map (·.ty)) I.calldata =
      if ReallocateCalldataChecks I.calldata then some (reallocateCalldataLocals I.calldata) else none := by
  rw [reallocateDecodeRaw hsel]
  have h4 := calldata_size_ge_of_selIs I (metaMorphoV1_1SelBytes 34) rfl hsel
  by_cases hh : solcSLT (solcSub I.calldata.size 4) 32 = false
  · rw [hh]
    simp only [Bool.false_eq_true, if_false]
    have hb := (solcCalldataHeadCheck h4 hsize).mp hh
    by_cases ho : solcMaxU64 < (calldataWord I.calldata 4).toNat
    · rw [if_pos ho, if_neg (fun hc ↦ (Nat.not_lt.mpr hc.offset) ho)]
    rw [if_neg ho]
    change (if (decide (solcMaxU64 < (reallocateCount I.calldata).toNat) ||
        badExtent false false I.calldata.toList (reallocateArrayHead I.calldata).toNat
          (reallocateCount I.calldata).toNat 192) = true then none
      else some (reallocateCalldataLocals I.calldata)) = _
    by_cases hl : solcMaxU64 < (reallocateCount I.calldata).toNat
    · simp only [hl, decide_true, Bool.true_or, if_true,
        if_neg (fun (hc : ReallocateCalldataChecks I.calldata) ↦ (Nat.not_lt.mpr hc.length) hl)]
    simp only [hl, decide_false, Bool.false_or]
    by_cases he : badExtent false false I.calldata.toList (reallocateArrayHead I.calldata).toNat
        (reallocateCount I.calldata).toNat 192 = false
    · have hc := (reallocateBadExtentChecks (Nat.le_of_not_gt ho) (Nat.le_of_not_gt hl) hsize).mp he
      rw [he, if_neg (by decide), if_pos ⟨hb.1, hc.1, Nat.le_of_not_gt ho, Nat.le_of_not_gt hl, hc.2⟩]
    · rw [Bool.eq_true_of_not_eq_false he, if_pos rfl, if_neg (fun hc ↦ he
        ((reallocateBadExtentChecks hc.offset hc.length hsize).mpr ⟨hc.high, hc.extent⟩))]
  · rw [Bool.eq_true_of_not_eq_false hh, if_pos rfl, if_neg (fun hc ↦ hh
      ((solcCalldataHeadCheck h4 hsize).mpr ⟨hc.head, by have := hc.high; omega⟩))]

theorem ReallocateCalldataChecks.loopData {cd : ByteArray} (h : ReallocateCalldataChecks cd) :
    SourceMemory.ReallocateLoopData cd (reallocateInput cd) (calldataWord cd 4) (reallocateCount cd) := by
  refine ⟨h.high, h.extent, reallocateCalldataValues_length _ _, ?_⟩
  intro i hi
  have hh := reallocateArrayHead_toNat h.offset
  have ho : (calldataWord cd 4).toNat ≤ 2 ^ 64 - 1 := h.offset
  have hdata : (reallocateArrayHead cd + ⟨32⟩).toNat = (calldataWord cd 4).toNat + 36 := by
    have he : (reallocateArrayHead cd + (⟨32⟩ : UInt256)).toNat = (reallocateArrayHead cd).toNat + 32 :=
      uadd_word_ofNat_toNat (reallocateArrayHead cd) 32 (by rw [hh]; change _ < 2 ^ 256; omega)
    rw [he, hh]
    omega
  have hr := reallocateCalldataValues_getElem cd (reallocateArrayHead cd) i.toNat hi
  rw [hdata, SourceMemory.retainedReallocateRow (by omega)
      (by have := h.extent; omega) (by have := h.high; omega)] at hr
  simpa only [SourceMemory.reallocateRowBase_toNat h.high h.extent hi,
    show (calldataWord cd 4).toNat + 192 * i.toNat + 36 =
      (calldataWord cd 4).toNat + 36 + 192 * i.toNat by omega] using hr

end Benchmarks.Morpho.MetaMorphoV1_1
