import Benchmarks.CurveVault.SymbolReturnMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: an extending copy stores the available source bytes.
theorem write_gap_partial (src base : ByteArray) (srcOff dest len : Nat)
    (hpos : 0 < len) (hsrc : srcOff < src.size) (hge : base.size ≤ dest)
    (hgap : dest - base.size < USize.size) :
    src.write srcOff base dest len = base ++ ByteArray.zeroes (dest - base.size) ++
      src.extract srcOff (srcOff + len) := by
  let copied := min len (src.size - srcOff)
  have hcopied : 0 < copied := by dsimp only [copied]; omega
  have hc : srcOff + copied ≤ src.size := by dsimp only [copied]; omega
  have hwrite : src.write srcOff base dest len = src.write srcOff base dest copied := by
    unfold ByteArray.write
    rw [if_neg (by omega : len ≠ 0), if_neg (by omega : ¬ srcOff ≥ src.size),
      if_neg (by omega : copied ≠ 0), if_neg (by omega : ¬ srcOff ≥ src.size)]
    dsimp only
    have h1 : min base.size (dest + len) - (dest + min len (src.size - srcOff)) = 0 := by omega
    have h2 : min base.size (dest + copied) - (dest + min copied (src.size - srcOff)) = 0 := by omega
    rw [h1, h2, Nat.min_eq_left (show copied ≤ src.size - srcOff by omega)]
  rw [hwrite, write_from_gap_eq src base srcOff dest copied (by omega) hc hge hgap]
  congr 1
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [← byteArray_toList_eq, byteArray_extract_toList, Nat.add_sub_cancel_left]
  rw [List.take_eq_take_iff]
  simp only [List.length_drop, byteArray_toList_eq, Array.length_toList, ByteArray.size_data]
  dsimp only [copied]
  omega

theorem paddedSource_extract (src : ByteArray) (srcOff len : Nat)
    (hpos : 0 < len) (hsrc : srcOff < src.size) (hlen : len ≤ src.size) :
    (src ++ ByteArray.zeroes (len - min len (src.size - srcOff))).extract srcOff (srcOff + len) =
      src.readWithPadding srcOff len := by
  by_cases hfull : srcOff + len ≤ src.size
  · rw [Nat.min_eq_left (by omega : len ≤ src.size - srcOff), Nat.sub_self,
      zeroes_zero (n := 0) (by rfl)]
    have happ : src ++ ByteArray.empty = src := by
      apply ByteArray.ext
      simp only [ByteArray.data_append, show ByteArray.empty.data = #[] from rfl, Array.append_empty]
    rw [happ, readWithPadding_eq_extract_unbounded src srcOff len hpos hfull]
  · have hpad : len - min len (src.size - srcOff) = srcOff + len - src.size := by omega
    have hext : src.extract srcOff (srcOff + len) = src.extract srcOff src.size := by
      apply ByteArray.ext
      simp only [ByteArray.data_extract, Array.extract_eq_extract_right, ByteArray.size_data]
      omega
    rw [hpad, extract_append_span _ _ _ _ (by omega) (by omega)]
    have hz : (ByteArray.zeroes (srcOff + len - src.size)).extract 0 (srcOff + len - src.size) =
        ByteArray.zeroes (srcOff + len - src.size) := by
      simpa only [ByteArray_zeroes_size] using byteArray_extract_self (ByteArray.zeroes (srcOff + len - src.size))
    rw [hz]
    unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
    rw [if_neg (by omega : ¬ srcOff ≥ src.size), Nat.min_eq_left hlen, hext]
    dsimp only
    rw [ByteArray.size_extract, Nat.min_self,
      show len - (src.size - srcOff) = srcOff + len - src.size by omega]

-- LIBRARY CANDIDATE: an in-bounds copy pads a short source with zero bytes.
theorem write_inBounds_padded (src base : ByteArray) (srcOff dest len : Nat)
    (hpos : 0 < len) (hsrc : srcOff < src.size) (hlen : len ≤ src.size)
    (hfit : dest + len ≤ base.size) :
    src.write srcOff base dest len = base.extract 0 dest ++
      src.readWithPadding srcOff len ++ base.extract (dest + len) base.size := by
  let copied := min len (src.size - srcOff)
  let padded := src ++ ByteArray.zeroes (len - copied)
  have hcopied : copied ≤ len ∧ copied ≤ src.size - srcOff := by dsimp only [copied]; omega
  have hpadded : srcOff + len ≤ padded.size := by
    dsimp only [padded]
    rw [ByteArray.size_append, ByteArray_zeroes_size]
    dsimp only [copied]
    omega
  have hwrite : src.write srcOff base dest len = padded.write srcOff base dest len := by
    unfold ByteArray.write
    rw [if_neg (by omega : len ≠ 0), if_neg (by omega : ¬ srcOff ≥ src.size),
      if_neg (by omega : ¬ srcOff ≥ padded.size)]
    simp only [if_neg (by omega : len ≠ 0)]
    have h1 : min base.size (dest + len) - (dest + min len (src.size - srcOff)) = len - copied := by omega
    have h2 : min len (padded.size - srcOff) = len := by omega
    have h3 : min base.size (dest + len) - (dest + len) = 0 := by omega
    rw [h1, h2, h3, Nat.add_zero]
    rw [show min len (src.size - srcOff) + (len - copied) = len by change copied + (len - copied) = len; omega]
    change padded.copySlice srcOff (base ++ ByteArray.zeroes (dest - base.size)) dest len =
      (padded ++ ByteArray.zeroes 0).copySlice srcOff (base ++ ByteArray.zeroes (dest - base.size)) dest len
    rw [zeroes_zero (n := 0) (by rfl)]
    have happ : padded ++ ByteArray.empty = padded := by
      apply ByteArray.ext
      simp only [ByteArray.data_append, show ByteArray.empty.data = #[] from rfl, Array.append_empty]
    rw [happ]
  rw [hwrite, copyWindow_eq padded base srcOff dest len (by omega) hpadded (by omega)]
  rw [show padded.extract srcOff (srcOff + len) = src.readWithPadding srcOff len from
    paddedSource_extract src srcOff len hpos hsrc hlen]

end Benchmarks.CurveVault
