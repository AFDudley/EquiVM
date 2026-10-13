import Benchmarks.Safe.V2_0e91d99.MemoryBytesDecoded

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V2_0e91d99

set_option maxRecDepth 1000

def delegationPrefix (code : ByteArray) : ByteArray :=
  code.extract 0 3 ++ ByteArray.mk (Array.replicate (3 - (code.extract 0 3).size) 0)

theorem delegationPrefix_size (code : ByteArray) : (delegationPrefix code).size = 3 := by
  unfold delegationPrefix
  rw [ByteArray.size_append]
  change (code.extract 0 3).size +
    (Array.replicate (3 - (code.extract 0 3).size) (0 : UInt8)).size = 3
  rw [Array.size_replicate, ByteArray.size_extract]
  omega

theorem delegationCopy (code mem : ByteArray) (hm : 3 ≤ mem.size) :
    code.write 0 mem 0 3 = delegationPrefix code ++ mem.extract 3 mem.size := by
  apply ByteArray.ext
  simp only [ByteArray.write, delegationPrefix, Nat.zero_add, Nat.sub_zero,
    show (3 : Nat) ≠ 0 by decide, if_false, Nat.zero_sub,
    Nat.min_eq_left hm, ByteArray.size_extract, ByteArray.data_append,
    ByteArray.data_extract]
  split
  · have hz : code.size = 0 := by omega
    have he : code = ByteArray.empty := ByteArray.ext (Array.eq_empty_of_size_eq_zero hz)
    subst code
    simp only [ByteArray.data_copySlice, ByteArray.zeroes, ByteArray.empty,
      ByteArray.emptyWithCapacity, ByteArray.size, Nat.zero_min, Nat.zero_add,
      Nat.sub_zero, Array.size_replicate, Array.extract_replicate, Nat.min_self]
    rw [Array.extract_eq_empty_of_le (by omega : min 0 mem.data.size ≤ 0),
      Array.empty_append]
    rfl
  · have hm' : 3 ≤ mem.data.size := hm
    have hadd : min 3 code.size + (3 - min 3 code.size) = 3 := by omega
    simp only [ByteArray.data_copySlice, ByteArray.zeroes, ByteArray.data_append,
      Array.replicate_zero, Array.append_empty, Nat.min_eq_right hm,
      Nat.zero_add, Nat.sub_zero, hadd,
      Array.size_append, Array.size_replicate,
      Array.extract_eq_empty_of_le (by omega : min 0 mem.data.size ≤ 0),
      Array.empty_append]
    have hsrc : 3 ≤ code.data.size + (3 - min 3 code.size) := by change 3 ≤ code.size + _; omega
    rw [Nat.min_eq_left hsrc, Array.extract_append]
    simp only [Array.extract_replicate]
    congr 2
    congr 1
    change min (3 - code.size) (3 - min 3 code.size) - (0 - code.size) = 3 - min 3 code.size
    omega

theorem delegationCopy_size (code mem : ByteArray) (hm : 3 ≤ mem.size) :
    (code.write 0 mem 0 3).size = mem.size := by
  rw [delegationCopy code mem hm, ByteArray.size_append, delegationPrefix_size,
    ByteArray.size_extract]
  omega

theorem delegationCopy_read (code mem : ByteArray) (off count : Nat)
    (hm : 3 ≤ mem.size) (ho : 3 ≤ off) (hin : off + count ≤ mem.size) :
    (code.write 0 mem 0 3).readWithPadding off count = mem.readWithPadding off count := by
  by_cases hz : count = 0
  · simp only [hz, byteArray_readWithPadding_zero]
  rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega) (by
      rw [delegationCopy_size code mem hm]; exact hin),
    readWithPadding_eq_extract_unbounded _ _ _ (by omega) hin,
    delegationCopy code mem hm,
    extract_append_right_window _ _ _ _ (by rw [delegationPrefix_size]; omega),
    delegationPrefix_size, extract_extract_BA]
  congr 1 <;> omega

theorem delegationLoadPrefix (code mem : ByteArray) (hm : 32 ≤ mem.size) :
    (memLoad ⟨0⟩ (code.write 0 mem 0 3)).toByteArray.extract 0 3 =
      delegationPrefix code := by
  have hs := delegationCopy_size code mem (by omega)
  rw [memLoadReadWord, uInt256OfByteArray_eq]
  change (UInt256.ofNat (fromByteArrayBigEndian
    ((code.write 0 mem 0 3).readWithPadding 0 32))).toByteArray.extract 0 (0 + 3) = _
  rw [toByteArray_readWord_extract _ 0 0 3 (by omega) (by decide) (by decide)]
  rw [readWithPadding_eq_extract_unbounded _ _ _ (by decide) (by omega),
    delegationCopy code mem (by omega),
    extract_append_left _ _ _ _ (by rw [delegationPrefix_size])]
  rw [← delegationPrefix_size code]
  simpa only [Nat.zero_add] using byteArray_extract_self (delegationPrefix code)

theorem delegationShift (w : UInt256) :
    (UInt256.shiftRight w ⟨232⟩).toNat =
      fromBytesBigEndian (w.toByteArray.extract 0 3).toList := by
  rw [bytesBE_extract_high w 3 (by decide)]
  unfold UInt256.shiftRight UInt256.toNat
  rw [if_neg (by decide)]
  change (w.val >>> (⟨232⟩ : UInt256).val).val = w.val.val / 2 ^ 232
  rw [Fin.shiftRight_val, Nat.shiftRight_eq_div_pow]
  rfl

theorem delegationWord (code mem : ByteArray) (hm : 32 ≤ mem.size) :
    UInt256.eq ⟨15663360⟩ (UInt256.shiftRight (memLoad ⟨0⟩ (code.write 0 mem 0 3)) ⟨232⟩) =
      if delegationPrefix code = ⟨#[0xef, 0x01, 0x00]⟩ then ⟨1⟩ else ⟨0⟩ := by
  have hn := delegationShift (memLoad ⟨0⟩ (code.write 0 mem 0 3))
  rw [delegationLoadPrefix code mem hm] at hn
  by_cases hd : delegationPrefix code = ⟨#[0xef, 0x01, 0x00]⟩
  · have hw : UInt256.shiftRight (memLoad ⟨0⟩ (code.write 0 mem 0 3)) ⟨232⟩ = ⟨15663360⟩ := by
      apply u256_inj
      rw [hn, hd]
      native_decide
    rw [if_pos hd, hw, uInt256_eq_self]
  · rw [if_neg hd]
    apply uInt256_eq_zero_of_ne
    intro he
    apply hd
    have hnum := congrArg UInt256.toNat (uInt256_eq_one_eq he).symm
    rw [hn] at hnum
    apply ByteArray.ext
    apply Array.toList_inj.mp
    apply fromBytesBigEndian_inj_of_length
    · change (delegationPrefix code).size = 3
      exact delegationPrefix_size code
    · simpa only [byteArray_toList_eq] using hnum.trans (show (⟨15663360⟩ : UInt256).toNat =
        fromBytesBigEndian [0xef, 0x01, 0x00] by native_decide)

end Benchmarks.Safe.V2_0e91d99
