import Benchmarks.CurveVault.PaddedCopyMemory
import Benchmarks.CurveVault.StringMemory
import Benchmarks.CurveVault.PaddedReadMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.CurveVault

def vaultInitializeCopyMemory (mem : ByteArray) (ptr : UInt256) : ByteArray :=
  let temp := mem.write ptr.toNat mem 416 64
  temp.write 416 temp 224 64

theorem vaultInitializeCopyMemory_words (mem : ByteArray) (ptr size : UInt256)
    (hbound : mem.size ≤ 384) (hptr : ptr.toNat ≤ 352) (hfull : ptr.toNat + 32 ≤ mem.size)
    (hsize : memLoad ptr mem = size) :
    let word := memLoad (UInt256.ofNat (ptr.toNat + 32)) mem
    memLoad (UInt256.ofNat 224) (vaultInitializeCopyMemory mem ptr) = size ∧
    memLoad (UInt256.ofNat 256) (vaultInitializeCopyMemory mem ptr) = word ∧
    memLoad (UInt256.ofNat 416) (vaultInitializeCopyMemory mem ptr) = size ∧
    448 ≤ (vaultInitializeCopyMemory mem ptr).size ∧
    (vaultInitializeCopyMemory mem ptr).size ≤ 480 := by
  let pre := mem ++ ByteArray.zeroes (416 - mem.size)
  let chunk := mem.extract ptr.toNat (ptr.toNat + 64)
  let temp := mem.write ptr.toNat mem 416 64
  have hp : pre.size = 416 := by
    rw [ByteArray.size_append, ByteArray_zeroes_size]
    omega
  have hb : 32 ≤ chunk.size ∧ chunk.size ≤ 64 := by
    dsimp only [chunk]
    rw [ByteArray.size_extract]
    omega
  have ht : temp = pre ++ chunk :=
    write_gap_partial mem mem ptr.toNat 416 64 (by omega) (by omega) (by omega)
      (lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize 416 (by omega)))
  have htSize : temp.size = 416 + chunk.size := by rw [ht, ByteArray.size_append, hp]
  have hread0 : temp.readWithPadding 416 32 = mem.readWithPadding ptr.toNat 32 := by
    rw [ht]
    simpa only [hp, Nat.add_zero] using (readWithPadding_append_right32 pre chunk 0 hb.1).trans
      (readWithPadding_extract32 mem ptr.toNat (ptr.toNat + 64) 0 hb.1 (by omega))
  have hread1 : temp.readWithPadding 448 32 = mem.readWithPadding (ptr.toNat + 32) 32 := by
    rw [ht, show 448 = pre.size + 32 by omega, readWithPadding_append_right32 pre chunk 32 hb.1]
    exact readWithPadding_extract32 mem ptr.toNat (ptr.toNat + 64) 32 hb.1 (by omega)
  let word := memLoad (UInt256.ofNat (ptr.toNat + 32)) mem
  have hw : word.toByteArray = mem.readWithPadding (ptr.toNat + 32) 32 := by
    simpa only [ulit_toNat' (ptr.toNat + 32) (by change ptr.toNat + 32 < 2 ^ 256; omega)] using
      memLoad_toByteArray mem (UInt256.ofNat (ptr.toNat + 32))
  have hs : size.toByteArray = mem.readWithPadding ptr.toNat 32 := by
    rw [← hsize]
    exact memLoad_toByteArray mem ptr
  have hread : temp.readWithPadding 416 64 = size.toByteArray ++ word.toByteArray := by
    rw [readWithPadding_split32_first temp 416 (by omega) (by omega), hread0, hread1, ← hs, ← hw]
  have hmem : vaultInitializeCopyMemory mem ptr =
      temp.extract 0 224 ++ (size.toByteArray ++ word.toByteArray) ++ temp.extract 288 temp.size := by
    change temp.write 416 temp 224 64 = _
    rw [write_inBounds_padded temp temp 416 224 64 (by omega) (by omega) (by omega) (by omega), hread]
  have hprefix : (temp.extract 0 224).size = 224 := by rw [ByteArray.size_extract]; omega
  have hprefix1 : (temp.extract 0 224 ++ size.toByteArray).size = 256 := by
    rw [ByteArray.size_append, hprefix, toByteArray_size]
  have hfinalSize : (vaultInitializeCopyMemory mem ptr).size = temp.size := by
    rw [hmem, ByteArray.size_append, ByteArray.size_append, hprefix,
      ByteArray.size_append, toByteArray_size, toByteArray_size, ByteArray.size_extract]
    omega
  refine ⟨?_, ?_, ?_, by omega, by omega⟩
  · rw [hmem]
    simpa only [hprefix, ByteArray.append_assoc] using memLoad_append_word (temp.extract 0 224)
      (word.toByteArray ++ temp.extract 288 temp.size) size (by rw [hprefix]; decide +kernel)
  · rw [hmem]
    simpa only [hprefix1, ByteArray.append_assoc] using memLoad_append_word (temp.extract 0 224 ++ size.toByteArray)
      (temp.extract 288 temp.size) word (by rw [hprefix1]; decide +kernel)
  · apply Reasoning.VyperCalls.memLoad_of_read _ _ _ (by decide +kernel) (by omega)
    rw [readWithPadding_eq_extract _ _ (by omega), hmem]
    have hcore : (temp.extract 0 224 ++ (size.toByteArray ++ word.toByteArray)).size = 288 := by
      rw [ByteArray.size_append, hprefix, ByteArray.size_append, toByteArray_size, toByteArray_size]
    rw [extract_append_right_window _ _ _ _ (by rw [hcore]; omega), hcore, extract_extract_BA]
    change temp.extract 416 (min 448 temp.size) = size.toByteArray
    rw [Nat.min_eq_left (by omega), ← readWithPadding_eq_extract temp 416 (by omega), hread0, ← hs]

end Benchmarks.CurveVault
