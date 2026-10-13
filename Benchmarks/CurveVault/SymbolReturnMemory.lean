import Benchmarks.CurveVault.SymbolReturnABI

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: padded words in the right part of an append.
theorem readWithPadding_append_right32 (a b : ByteArray) (off : Nat) (hb : 32 ≤ b.size) :
    (a ++ b).readWithPadding (a.size + off) 32 = b.readWithPadding off 32 := by
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  rw [ByteArray.size_append]
  by_cases h : b.size ≤ off
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h, Nat.min_eq_left (show 32 ≤ a.size + b.size by omega),
      Nat.min_eq_left hb, extract_append_right_window _ _ _ _ (by omega)]
    simp only [Nat.add_sub_cancel_left, Nat.add_assoc]

theorem memLoad_append_right (a b : ByteArray) (off : Nat) (hb : 32 ≤ b.size)
    (hfit : a.size + off < UInt256.size) :
    memLoad (UInt256.ofNat (a.size + off)) (a ++ b) = memLoad (UInt256.ofNat off) b := by
  unfold memLoad
  rw [ulit_toNat' _ hfit, ulit_toNat' off (by omega), ByteArray.size_append]
  by_cases h : b.size ≤ off
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h, readWithPadding_append_right32 _ _ _ hb]

theorem memLoad_toByteArray (mem : ByteArray) (off : UInt256) :
    (memLoad off mem).toByteArray = mem.readWithPadding off.toNat 32 := by
  unfold memLoad
  split
  · rw [zero_toByteArray_eq_zeroes32]
    simp only [ByteArray.readWithPadding, ByteArray.readWithoutPadding, if_pos (by assumption),
      ByteArray.size_empty, Nat.sub_zero, empty_append]
  · exact toByteArray_ofNat_fromByteArrayBigEndian_of_size (readWithPadding_size _ _ _)

def vaultSymbolCallMemory (mem out : ByteArray) : ByteArray :=
  mem.extract 0 288 ++ out.extract 0 96

theorem vaultSymbolCallMemory_eq (mem out : ByteArray) (hmem : mem.size = 320)
    (h32 : 32 ≤ out.size) (hwide : out.size < UInt256.size) :
    out.write 0 mem 288 (min (UInt256.ofNat 96) (UInt256.ofNat out.size)).toNat =
      vaultSymbolCallMemory mem out := by
  rw [callOutputLen _ _ hwide (by decide +kernel),
    copyWindow_eq out mem 0 288 (min out.size 96) (by omega) (by omega) (by omega)]
  have htail : mem.extract (288 + min out.size 96) mem.size = ByteArray.empty := by
    exact byteArray_extract_empty_of_le mem (by omega)
  rw [htail]
  have hnil (b : ByteArray) : b ++ ByteArray.empty = b := by
    apply ByteArray.ext
    rw [ByteArray.data_append]
    change b.data ++ #[] = b.data
    exact Array.append_empty
  rw [hnil]
  unfold vaultSymbolCallMemory
  congr 1
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [← byteArray_toList_eq, byteArray_extract_toList, List.drop_zero, Nat.sub_zero, List.take_take]
  rw [List.take_eq_take_iff]
  simp only [byteArray_toList_eq, Array.length_toList]
  simp only [Nat.zero_add, ByteArray.size_data]
  omega

theorem vaultSymbolCallMemory_size (mem out : ByteArray) (hmem : mem.size = 320) :
    (vaultSymbolCallMemory mem out).size = 288 + min out.size 96 := by
  simp only [vaultSymbolCallMemory, ByteArray.size_append, ByteArray.size_extract, hmem]
  omega

theorem vaultSymbolCallMemory_load (mem out : ByteArray) (off : Nat) (hmem : mem.size = 320)
    (h32 : 32 ≤ out.size) (hfit : 288 + off < UInt256.size) :
    memLoad (UInt256.ofNat (288 + off)) (vaultSymbolCallMemory mem out) =
      memLoad (UInt256.ofNat off) (out.extract 0 96) := by
  have hp : (mem.extract 0 288).size = 288 := by rw [ByteArray.size_extract, hmem]; rfl
  simpa only [hp] using memLoad_append_right (mem.extract 0 288) (out.extract 0 96) off
    (by rw [ByteArray.size_extract]; omega) (by rw [hp]; exact hfit)

theorem vaultSymbolCallMemory_read (mem out : ByteArray) (off : Nat) (hmem : mem.size = 320)
    (h32 : 32 ≤ out.size) :
    (vaultSymbolCallMemory mem out).readWithPadding (288 + off) 32 =
      (out.extract 0 96).readWithPadding off 32 := by
  have hp : (mem.extract 0 288).size = 288 := by rw [ByteArray.size_extract, hmem]; rfl
  simpa only [hp] using readWithPadding_append_right32 (mem.extract 0 288) (out.extract 0 96) off
    (by rw [ByteArray.size_extract]; omega)

end Benchmarks.CurveVault
