import Benchmarks.CurveVault.StringScratchMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultStringPrepared (mem : ByteArray) (prefixSize : Nat) (prefixWord : UInt256) : ByteArray :=
  writeWord (writeWord mem 288 (UInt256.ofNat prefixSize)) 320 prefixWord

def vaultStringStaged (mem : ByteArray) (prefixSize : Nat) (prefixWord : UInt256) : ByteArray :=
  writeWord (vaultStringPrepared mem prefixSize prefixWord) 384 prefixWord

theorem vaultStringScratch_inputs (mem : ByteArray) (prefixSize : Nat) (prefixWord size word : UInt256)
    (hmem : 448 ≤ mem.size) (hn : memLoad (UInt256.ofNat 224) mem = size)
    (hw : memLoad (UInt256.ofNat 256) mem = word) :
    memLoad (UInt256.ofNat 288) (vaultStringPrepared mem prefixSize prefixWord) = UInt256.ofNat prefixSize ∧
    memLoad (UInt256.ofNat 320) (vaultStringPrepared mem prefixSize prefixWord) = prefixWord ∧
    memLoad (UInt256.ofNat 224) (vaultStringStaged mem prefixSize prefixWord) = size ∧
    memLoad (UInt256.ofNat 256) (vaultStringStaged mem prefixSize prefixWord) = word := by
  let m1 := writeWord mem 288 (UInt256.ofNat prefixSize)
  let m2 := vaultStringPrepared mem prefixSize prefixWord
  let m3 := vaultStringStaged mem prefixSize prefixWord
  have gap (off : Nat) (hsmall : off ≤ 384) (m : ByteArray) : off - m.size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) (lt_usize off (by omega))
  have hf1 : WordMemoryRange mem m1 0 288 :=
    wordMemoryRange_write _ _ _ _ _ (gap _ (by omega) _) (Or.inl (by omega))
  have hf2 : WordMemoryRange m1 m2 0 288 :=
    wordMemoryRange_write _ _ _ _ _ (gap _ (by omega) _) (Or.inl (by omega))
  have hf3 : WordMemoryRange m2 m3 0 288 :=
    wordMemoryRange_write _ _ _ _ _ (gap _ (by omega) _) (Or.inl (by omega))
  have hf := hf1.trans (hf2.trans hf3)
  refine ⟨?_, memLoad_write_back _ _ 320 (by decide +kernel) (gap _ (by omega) _),
    (hf.load 224 (by omega) (by omega) (by omega) (by decide +kernel)).trans hn,
    (hf.load 256 (by omega) (by omega) (by omega) (by decide +kernel)).trans hw⟩
  change memLoad (UInt256.ofNat 288) (prefixWord.toByteArray.write 0 m1 320 32) = _
  rw [memLoad_below_write _ _ 320 288 (by have := hf1.size; omega) (by omega)
    (gap _ (by omega) _) (by decide +kernel)]
  exact memLoad_write_back _ _ 288 (by decide +kernel) (gap _ (by omega) _)

theorem memLoad_read_window (mem : ByteArray) (off start len : Nat) (word : UInt256)
    (hoff : off < UInt256.size) (hfull : off + 32 ≤ mem.size)
    (hword : memLoad (UInt256.ofNat off) mem = word)
    (hwin : start + len ≤ 32) (hpos : 0 < len) :
    mem.readWithPadding (off + start) len = word.toByteArray.extract start (start + len) := by
  have hw : UInt256.ofNat (fromByteArrayBigEndian (mem.readWithPadding off 32)) = word := by
    simpa only [memLoad, ulit_toNat' off hoff, if_neg (show ¬ off ≥ mem.size by omega)] using hword
  rw [← hw]
  exact (toByteArray_readWord_extract mem off start len hfull hwin hpos).symm

end Benchmarks.CurveVault
