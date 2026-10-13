import Benchmarks.CurveVault.SymbolReturnMemory

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: a padded read, including one starting beyond memory.
theorem readWithPadding_extract_pad (mem : ByteArray) (off len : Nat) (hlen : len ≤ mem.size) :
    mem.readWithPadding off len = mem.extract off (off + len) ++
      ByteArray.zeroes (len - (mem.extract off (off + len)).size) := by
  by_cases h : mem.size ≤ off
  · have hext : mem.extract off (off + len) = ByteArray.empty := by
      apply byteArray_eq_empty_of_size_eq_zero
      rw [ByteArray.size_extract]
      omega
    simp only [ByteArray.readWithPadding, ByteArray.readWithoutPadding, if_pos h, hext]
  · simp only [ByteArray.readWithPadding, ByteArray.readWithoutPadding, if_neg h, Nat.min_eq_left hlen]

-- LIBRARY CANDIDATE: split two padded words when the first word is present.
theorem readWithPadding_split32_first (mem : ByteArray) (off : Nat)
    (hlen : 64 ≤ mem.size) (hfirst : off + 32 ≤ mem.size) :
    mem.readWithPadding off 64 = mem.readWithPadding off 32 ++ mem.readWithPadding (off + 32) 32 := by
  rw [readWithPadding_extract_pad mem off 64 hlen,
    readWithPadding_eq_extract mem off hfirst,
    readWithPadding_extract_pad mem (off + 32) 32 (by omega)]
  have hsplit : mem.extract off (off + 64) =
      mem.extract off (off + 32) ++ mem.extract (off + 32) (off + 32 + 32) := by
    rw [ByteArray.extract_append_extract]
    congr 1 <;> omega
  rw [hsplit, ByteArray.size_append, ByteArray.size_extract (b := off)]
  have hfirstSize : min (off + 32) mem.size - off = 32 := by omega
  rw [hfirstSize, show 64 - (32 + (mem.extract (off + 32) (off + 32 + 32)).size) =
    32 - (mem.extract (off + 32) (off + 32 + 32)).size by omega]
  apply ByteArray.ext
  simp only [ByteArray.data_append, Array.append_assoc]

-- LIBRARY CANDIDATE: truncation beyond a word does not change its padded read.
theorem readWithPadding_extract32 (mem : ByteArray) (start stop off : Nat)
    (hsize : 32 ≤ (mem.extract start stop).size) (hwin : start + off + 32 ≤ stop) :
    (mem.extract start stop).readWithPadding off 32 = mem.readWithPadding (start + off) 32 := by
  have hlength : (mem.extract start stop).size = min stop mem.size - start := ByteArray.size_extract
  have hm32 : 32 ≤ mem.size := by omega
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  by_cases h : (mem.extract start stop).size ≤ off
  · rw [if_pos h, if_pos (show mem.size ≤ start + off by omega)]
  · rw [if_neg h, if_neg (show ¬ mem.size ≤ start + off by omega),
      Nat.min_eq_left hsize, Nat.min_eq_left hm32]
    dsimp only
    rw [extract_extract_BA, Nat.min_eq_left (show start + (off + 32) ≤ stop by omega)]
    rw [Nat.add_assoc]

end Benchmarks.CurveVault
