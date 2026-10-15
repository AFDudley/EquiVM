import Benchmarks.CurveVault.Memory
import Benchmarks.CurveVault.SymbolReturnMemory

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultStringScratch (mem : ByteArray) (prefixSize : Nat) (prefixWord size word : UInt256) : ByteArray :=
  writeCascade mem [(288, UInt256.ofNat prefixSize), (320, prefixWord), (384, prefixWord),
    (384 + prefixSize, word), (352, UInt256.ofNat prefixSize + size)]

theorem vaultStringScratch_size (mem : ByteArray) (prefixSize : Nat) (prefixWord size word : UInt256)
    (hmem : 448 ≤ mem.size) (hp : prefixSize ≤ 16) :
    (vaultStringScratch mem prefixSize prefixWord size word).size = mem.size := by
  unfold vaultStringScratch
  rw [writeCascade_size]
  · simp only [writeCascadeSize]
    omega
  · simp only [WriteGapsOk, and_true]
    have hu : 0 < USize.size := lt_usize 0 (by omega)
    omega

theorem vaultStringScratch_frame (mem : ByteArray) (prefixSize : Nat) (prefixWord size word : UInt256)
    (hmem : 448 ≤ mem.size) (hp : prefixSize ≤ 16) :
    WordMemoryRange mem (vaultStringScratch mem prefixSize prefixWord size word) 0 288 := by
  let m1 := writeWord mem 288 (UInt256.ofNat prefixSize)
  let m2 := writeWord m1 320 prefixWord
  let m3 := writeWord m2 384 prefixWord
  let m4 := writeWord m3 (384 + prefixSize) word
  have gap (m : ByteArray) (off : Nat) (hin : off ≤ m.size) : off - m.size < USize.size := by
    have hu := lt_usize 0 (by omega)
    omega
  have hf1 : WordMemoryRange mem m1 0 288 := wordMemoryRange_write _ _ _ _ _ (gap _ _ (by omega)) (Or.inl (by omega))
  have hf2 : WordMemoryRange m1 m2 0 288 := wordMemoryRange_write _ _ _ _ _ (gap _ _ (by have := hf1.size; omega)) (Or.inl (by omega))
  have hf3 : WordMemoryRange m2 m3 0 288 := wordMemoryRange_write _ _ _ _ _ (gap _ _ (by have := hf1.size; have := hf2.size; omega)) (Or.inl (by omega))
  have hf4 : WordMemoryRange m3 m4 0 288 := wordMemoryRange_write _ _ _ _ _
    (gap _ _ (by have := hf1.size; have := hf2.size; have := hf3.size; omega)) (Or.inl (by omega))
  exact hf1.trans (hf2.trans (hf3.trans (hf4.trans
    (wordMemoryRange_write _ _ 352 0 288 (gap _ _ (by
      have := hf1.size; have := hf2.size; have := hf3.size; have := hf4.size; omega)) (Or.inl (by omega))))))

theorem vaultStringScratch_header (mem : ByteArray) (prefixSize : Nat) (prefixWord size word : UInt256) :
    memLoad (UInt256.ofNat 352) (vaultStringScratch mem prefixSize prefixWord size word) =
      UInt256.ofNat prefixSize + size := by
  exact memLoad_write_back _ _ 352 (by decide +kernel)
    (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 352 (by omega)))

theorem vaultStringScratch_payload (mem : ByteArray) (prefixSize : Nat) (prefixWord size word : UInt256)
    (hmem : 448 ≤ mem.size) (hp0 : 0 < prefixSize) (hp : prefixSize ≤ 16) :
    (vaultStringScratch mem prefixSize prefixWord size word).readWithPadding 384 64 =
      prefixWord.toByteArray.extract 0 prefixSize ++ word.toByteArray ++
        mem.readWithPadding (416 + prefixSize) (32 - prefixSize) := by
  let m1 := writeWord mem 288 (UInt256.ofNat prefixSize)
  let m2 := writeWord m1 320 prefixWord
  let m3 := writeWord m2 384 prefixWord
  let writes := [(288, UInt256.ofNat prefixSize), (320, prefixWord), (384, prefixWord),
    (384 + prefixSize, word), (352, UInt256.ofNat prefixSize + size)]
  have hu : 0 < USize.size := lt_usize 0 (by omega)
  have hs1 : m1.size = mem.size := by
    rw [writeWord_size _ _ _ (by omega)]
    omega
  have hs2 : m2.size = mem.size := by
    rw [writeWord_size _ _ _ (by omega), hs1]
    omega
  have hs3 : m3.size = mem.size := by
    rw [writeWord_size _ _ _ (by omega), hs2]
    omega
  have hpre : (vaultStringScratch mem prefixSize prefixWord size word).readWithPadding 384 prefixSize =
      prefixWord.toByteArray.extract 0 prefixSize := by
    change (writeCascade m2 [(384, prefixWord), (384 + prefixSize, word),
      (352, UInt256.ofNat prefixSize + size)]).readWithPadding (384 + 0) prefixSize = _
    simpa only [Nat.zero_add] using writeCascade_read_window_of_head m2 384 0 prefixSize prefixWord _
      (by omega) (by simp only [WindowDisjointFromWrites, and_true]; omega) (by omega) hp0 (by omega)
  have hword : (vaultStringScratch mem prefixSize prefixWord size word).readWithPadding (384 + prefixSize) 32 =
      word.toByteArray := by
    change (writeCascade m3 [(384 + prefixSize, word), (352, UInt256.ofNat prefixSize + size)]).readWithPadding
      (384 + prefixSize) 32 = _
    exact writeCascade_read_word_of_head m3 _ _ _ (by omega)
      (by simp only [WindowDisjointFromWrites, and_true]; omega)
  have htail : (vaultStringScratch mem prefixSize prefixWord size word).readWithPadding (416 + prefixSize) (32 - prefixSize) =
      mem.readWithPadding (416 + prefixSize) (32 - prefixSize) := by
    exact writeCascade_read_preserved_len mem writes _ _
      (by simp only [writes, WindowDisjointFromWrites, and_true]; omega) (by omega) (by omega)
  have hsz := vaultStringScratch_size mem prefixSize prefixWord size word hmem hp
  have h64 : 64 = prefixSize + (32 + (32 - prefixSize)) := by omega
  rw [h64, byteArray_readWithPadding_split_unbounded _ 384 prefixSize (32 + (32 - prefixSize)) hp0 (by omega) (by omega),
    byteArray_readWithPadding_split_unbounded _ (384 + prefixSize) 32 (32 - prefixSize) (by omega) (by omega) (by omega),
    hpre, hword, show 384 + prefixSize + 32 = 416 + prefixSize by omega, htail, ByteArray.append_assoc]

end Benchmarks.CurveVault
