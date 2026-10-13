import Benchmarks.EAS.EAS.WordArrayBase
import Benchmarks.EAS.EAS.ReturnDecode
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- GENERALIZES solcReadBytes_word to arbitrary complete slices.
theorem solcReadBytes_extract {out : ByteArray} {start size : Nat}
    (hs : start < UInt256.size) (hb : start + size ≤ out.size) :
    solcReadBytes out.toList start size = (out.extract start (start+size)).toList := by
  have hl : out.toList.length = out.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have ht : ((out.toList.drop start).take size).length = size := by
    rw [List.length_take, List.length_drop, hl]; omega
  have hs' : start < EVM.wordModulus := hs
  simp only [solcReadBytes, Nat.mod_eq_of_lt hs', ht, Nat.sub_self,
    List.replicate_zero, List.append_nil, extract_toList, Nat.add_sub_cancel_left]

-- LIBRARY CANDIDATE: decode a complete length-prefixed string slice.
theorem decodeStringSlice {out : ByteArray} {start len : Nat}
    (hh : start+32+len ≤ out.size) (hl : len ≤ solcMaxU64)
    (hw : (calldataWord out start).toNat = len) :
    decodeABIValue? .string (out.extract start (start+32+len)).toList 0 =
      some (.bytes (out.extract (start+32) (start+32+len)), 32+paddedSize len) := by
  let slice := out.extract start (start+32+len)
  have hs : slice.toList.length = 32+len := by
    rw [byteArray_toList_eq, Array.length_toList]
    change slice.size = 32+len
    rw [ByteArray.size_extract]
    omega
  have ht : (slice.toList.take 32).length = 32 := by rw [List.length_take, hs]; omega
  have hr : readNat? slice.toList 0 = some len := by
    simp only [readNat?, readWord?, readBytes?, List.drop_zero, ht, if_true, bind, Option.bind]
    have hword := decode_word_at_eq_any slice 0 (by change 0+32 ≤ slice.size; simp only [slice, ByteArray.size_extract]; omega)
    simp only [List.drop_zero] at hword
    rw [hword]
    change some (calldataWord (out.extract start (start+32+len)) 0).toNat = some len
    rw [calldataWord_extract_zero (start := start) (by omega) hh, hw]
  have hp : readBytes? slice.toList 32 len = some ((out.extract (start+32) (start+32+len)).toList) := by
    have ht' : ((slice.toList.drop 32).take len).length = len := by
      rw [List.length_take, List.length_drop, hs]; omega
    rw [readBytes?, if_pos ht']
    congr 1
    simp only [slice, extract_toList, List.drop_take, List.drop_drop, List.take_take,
      Nat.add_sub_cancel_left]
    congr 2 <;> omega
  change decodeABIValue? .string slice.toList 0 = _
  rw [decodeABIValue?, hr]
  simp only [solcMaxLen_modern, show ¬ solcMaxU64 < len by omega, if_false, bind,
    Option.bind, Nat.zero_add, hp]
  have he : (⟨(out.extract (start+32) (start+32+len)).toList.toArray⟩ : ByteArray) =
      out.extract (start+32) (start+32+len) := by
    apply byteArray_eq_of_toList_eq
    simp only [byteArray_toList_eq, List.toList_toArray]
  rw [he]

-- LIBRARY CANDIDATE: characterize a bounded materialized string decoder.
theorem decodeSolcString {out : ByteArray} {start : Nat}
    (hs : start+2^64+32 < 2^255) (hb : out.size < 2^255) :
    decodeValue? .string out.toList start {} =
      if start+32 ≤ out.size ∧ (calldataWord out start).toNat ≤ solcMaxU64 ∧
          start+32+(calldataWord out start).toNat ≤ out.size then
        some (.bytes (out.extract (start+32) (start+32+(calldataWord out start).toNat)))
      else none := by
  have hsize : out.size < UInt256.size := by change out.size < 2^256; omega
  have houtMod : out.size % EVM.wordModulus = out.size := Nat.mod_eq_of_lt hsize
  have hstart : start < UInt256.size := by change start < 2^256; omega
  have hlen : out.toList.length = out.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have h31 : solcAdd start 31 = start+31 := Nat.mod_eq_of_lt (by change start+31 < 2^256; omega)
  have h32 : solcAdd start 32 = start+32 := Nat.mod_eq_of_lt (by change start+32 < 2^256; omega)
  have hsign : solcSLT (solcAdd start 31) out.size = decide (start+31 < out.size) := by
    rw [h31, solcSLT_smallLeft (by omega) hsize]
    simp only [hb, and_true]
  rw [decodeValue?]
  change (if decide (solcMaxU64 < solcReadNat out.toList start) ||
    badExtent true false out.toList start (solcReadNat out.toList start) 1 then none else _) = _
  by_cases hh : start+32 ≤ out.size
  · rw [solcReadNat_word hh hsize]
    by_cases hl : (calldataWord out start).toNat ≤ solcMaxU64
    · have htotal : solcAdd (solcAdd start 32) ((calldataWord out start).toNat*1) =
          start+32+(calldataWord out start).toNat := by
        rw [h32, Nat.mul_one]
        apply Nat.mod_eq_of_lt
        change start+32+(calldataWord out start).toNat < 2^256
        change (calldataWord out start).toNat ≤ 18446744073709551615 at hl
        omega
      simp only [show ¬ solcMaxU64 < (calldataWord out start).toNat by omega,
        decide_false, Bool.false_or, badExtent, Bool.not_false, Bool.true_and,
        hlen, hsign, decide_eq_true (by omega : start+31 < out.size),
        Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false, Bool.false_or,
        houtMod, htotal]
      by_cases hp : start+32+(calldataWord out start).toNat ≤ out.size
      · simp only [show ¬ out.size < start+32+(calldataWord out start).toNat by omega,
          decide_false, Bool.false_eq_true, if_false]
        rw [solcReadBytes_extract hstart (by omega)]
        rw [show start+(32+(calldataWord out start).toNat) = start+32+(calldataWord out start).toNat by omega,
          decodeStringSlice hp hl rfl]
        simp only [Option.map_some, hh, hl, hp, and_self, if_true]
      · simp only [show out.size < start+32+(calldataWord out start).toNat by omega,
          decide_true, if_true, hp, and_false, if_false]
    · simp only [show solcMaxU64 < (calldataWord out start).toNat by omega,
        decide_true, Bool.true_or, if_true, hl, false_and, and_false, if_false]
  · have hc : ¬ start+31 < out.size := by omega
    simp only [badExtent, hlen, hsign, hc, decide_false, Bool.not_false,
      Bool.true_and, Bool.true_or, Bool.or_true, if_true, hh, false_and, if_false]

end Benchmarks.EAS.EAS
