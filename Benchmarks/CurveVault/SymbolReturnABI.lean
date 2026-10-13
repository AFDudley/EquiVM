import Benchmarks.CurveVault.Calls
import Benchmarks.CurveVault.StringGas

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperCalls Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: the bounded minimum idiom emitted by Vyper.
theorem vyperMin (n cap : Nat) (hn : n < UInt256.size) (hc : cap < UInt256.size) :
    UInt256.xor (UInt256.mul (UInt256.lt (UInt256.ofNat cap) (UInt256.ofNat n))
      (UInt256.xor (UInt256.ofNat n) (UInt256.ofNat cap))) (UInt256.ofNat n) =
      UInt256.ofNat (min n cap) := by
  by_cases h : cap < n
  · rw [ult_one (by rw [ulit_toNat' cap hc, ulit_toNat' n hn]; exact h),
      u256_one_mul, u256_xor_xor_cancel, Nat.min_eq_right (by omega)]
  · rw [ult_zero (by rw [ulit_toNat' cap hc, ulit_toNat' n hn]; omega),
      u256_mul_zero_left, u256_zero_xor, Nat.min_eq_left (by omega)]

theorem callOutputLen (n cap : Nat) (hn : n < UInt256.size) (hc : cap < UInt256.size) :
    (min (UInt256.ofNat cap) (UInt256.ofNat n)).toNat = min n cap := by
  by_cases h : cap ≤ n
  · have hw : UInt256.ofNat cap ≤ UInt256.ofNat n := by
      change (UInt256.ofNat cap).toNat ≤ (UInt256.ofNat n).toNat
      simpa only [ulit_toNat' cap hc, ulit_toNat' n hn] using h
    rw [Nat.min_eq_right h]
    simp only [min, hw, if_true, ulit_toNat' cap hc]
  · have hw : ¬ UInt256.ofNat cap ≤ UInt256.ofNat n := by
      change ¬ (UInt256.ofNat cap).toNat ≤ (UInt256.ofNat n).toNat
      simpa only [ulit_toNat' cap hc, ulit_toNat' n hn] using h
    rw [Nat.min_eq_left (Nat.le_of_not_ge h)]
    simp only [min, hw, if_false, ulit_toNat' n hn]

-- LIBRARY CANDIDATE: a complete ABI word is the corresponding memory load.
theorem readNat_memLoad (b : ByteArray) (off : Nat) (hoff : off < UInt256.size)
    (hfull : off + 32 ≤ b.size) :
    ABI.readNat? b.toList off = some (memLoad (UInt256.ofNat off) b).toNat := by
  have hlen : ((b.toList.drop off).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
    change min 32 (b.size - off) = 32
    omega
  have hbytes : (ByteArray.mk ((b.toList.drop off).take 32).toArray) = b.extract off (off + 32) := by
    apply ByteArray.ext
    apply Array.toList_inj.mp
    simp only [List.toList_toArray, ← byteArray_toList_eq, byteArray_extract_toList, Nat.add_sub_cancel_left]
  unfold ABI.readNat? ABI.readWord? ABI.readBytes?
  rw [if_pos hlen]
  simp only [Option.bind, bind]
  unfold ABI.bytesToWord
  rw [hbytes, ← readWithPadding_eq_extract b off hfull]
  simp only [memLoad, ulit_toNat' off hoff, if_neg (show ¬ off ≥ b.size by omega)]
  rfl

theorem readNat_short (b : ByteArray) (off : Nat) (hshort : b.size < off + 32) :
    ABI.readNat? b.toList off = none := by
  have hlen : ¬ ((b.toList.drop off).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
    change ¬ min 32 (b.size - off) = 32
    omega
  simp only [ABI.readNat?, ABI.readWord?, ABI.readBytes?, hlen, ↓reduceIte, Option.bind, bind]

def vaultBorrowedSymbol (size : Nat) (word : ByteArray) : Value :=
  .struct "EncodedSymbol" [("size", .int size), ("data", .fixedBytes ⟨31, by decide⟩ word.toList)]

theorem decodeTokenSymbol_short (out : ByteArray) (hshort : out.size < 32) :
    decodeTokenSymbol out = none := by
  dsimp only [decodeTokenSymbol]
  rw [readNat_short _ 0 (by rw [ByteArray.size_extract]; omega)]
  rfl

theorem decodeTokenSymbol_offset (out : ByteArray) (h32 : 32 ≤ out.size)
    (hshort : (out.extract 0 96).size < (memLoad (UInt256.ofNat 0) (out.extract 0 96)).toNat + 32) :
    decodeTokenSymbol out = none := by
  dsimp only [decodeTokenSymbol]
  rw [readNat_memLoad _ 0 (by decide +kernel) (by rw [ByteArray.size_extract]; omega)]
  simp only [Option.bind, bind]
  rw [readNat_short _ _ hshort]

theorem decodeTokenSymbol_eq (out : ByteArray) (h32 : 32 ≤ out.size)
    (hfull : (memLoad (UInt256.ofNat 0) (out.extract 0 96)).toNat + 32 ≤ (out.extract 0 96).size) :
    let copied := out.extract 0 96
    let offset := (memLoad (UInt256.ofNat 0) copied).toNat
    let size := (memLoad (UInt256.ofNat offset) copied).toNat
    decodeTokenSymbol out =
      if size > 32 ∨ copied.size < offset + 32 + size then none else
        some [vaultBorrowedSymbol size (copied.readWithPadding (offset + 32) 32)] := by
  dsimp only
  dsimp only [decodeTokenSymbol]
  rw [readNat_memLoad _ 0 (by decide +kernel) (by rw [ByteArray.size_extract]; omega)]
  simp only [Option.bind, bind]
  rw [readNat_memLoad (out.extract 0 96) (memLoad (UInt256.ofNat 0) (out.extract 0 96)).toNat
    (memLoad (UInt256.ofNat 0) (out.extract 0 96)).val.isLt hfull]
  simp only [Option.bind, bind, Bool.or_eq_true, decide_eq_true_eq]
  rfl

theorem decodeTokenSymbol_bounds (out : ByteArray) (h32 : 32 ≤ out.size)
    (hvalid : decodeTokenSymbol out ≠ none) :
    let copied := out.extract 0 96
    let offset := (memLoad (UInt256.ofNat 0) copied).toNat
    let size := (memLoad (UInt256.ofNat offset) copied).toNat
    offset + 32 ≤ copied.size ∧ size ≤ 32 ∧ offset + 32 + size ≤ copied.size := by
  dsimp only
  by_cases hfull : (memLoad (UInt256.ofNat 0) (out.extract 0 96)).toNat + 32 ≤ (out.extract 0 96).size
  · have hdecode := decodeTokenSymbol_eq out h32 hfull
    dsimp only at hdecode
    split at hdecode
    · exact False.elim (hvalid hdecode)
    · exact ⟨hfull, by omega, by omega⟩
  · exact False.elim (hvalid (decodeTokenSymbol_offset out h32 (by omega)))

end Benchmarks.CurveVault
