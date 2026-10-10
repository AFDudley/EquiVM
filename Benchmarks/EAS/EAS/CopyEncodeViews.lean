import Benchmarks.EAS.EAS.CopyViews
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: arbitrary in-bounds memory windows survive writes above them.
theorem writeWord_read_below_len (mem : ByteArray) (off read len : Nat) (word : UInt256)
    (hlo : read + len ≤ off) (hin : read + len ≤ mem.size) :
    (Reasoning.Theory.writeWord mem off word).readWithPadding read len = mem.readWithPadding read len := by
  by_cases hz : len = 0
  · simp only [hz, byteArray_readWithPadding_zero]
  have hp : 0 < len := by omega
  by_cases ho : off ≤ mem.size
  · exact toByteArray_write_read_below_len_of_gap_unbounded word mem off read len hin hlo hp
      (by rw [Nat.sub_eq_zero_of_le ho]; exact lt_usize 0 (by decide))
  · rw [writeWord_sparse_eq mem off word (by omega),
      readWithPadding_eq_extract_unbounded _ read len hp (by
        rw [ByteArray.size_append, ByteArray.size_append, ByteArray_zeroes_size, toByteArray_size]; omega),
      extract_append_left _ _ _ _ (by rw [ByteArray.size_append, ByteArray_zeroes_size]; omega),
      extract_append_left _ _ _ _ hin]
    exact (readWithPadding_eq_extract_unbounded mem read len hp hin).symm

theorem readWithPadding_prefix (mem : ByteArray) (off full len : Nat)
    (hlen : len ≤ full) (hin : off + full ≤ mem.size) :
    (mem.readWithPadding off full).extract 0 len = mem.readWithPadding off len := by
  by_cases hz : len = 0
  · rw [hz, byteArray_readWithPadding_zero]
    exact byteArray_extract_empty_of_le _ (by omega)
  rw [readWithPadding_eq_extract_unbounded _ _ full (by omega) hin, extract_extract_BA,
    readWithPadding_eq_extract_unbounded _ _ len (by omega) (by omega)]
  simp only [Nat.add_zero, Nat.min_eq_left (by omega : off + len ≤ off + full)]

theorem easCopyWords_read (src dst : UInt256) (mem : ByteArray) (n len : Nat)
    (hlo : 96 ≤ src.toNat) (hdisj : src.toNat + 32*n ≤ dst.toNat)
    (hin : src.toNat + 32*n ≤ mem.size) (hbound : dst.toNat + 32*n < UInt256.size)
    (hlen : len ≤ 32*n) :
    (easCopyWords src dst mem 0 n).readWithPadding dst.toNat len = mem.readWithPadding src.toNat len := by
  rw [easCopyWords_eq_sequence src dst mem 0 n (by omega) (by omega) (by omega) (by omega)]
  simp only [Nat.add_zero]
  rw [writeWordSequence_read_prefix _ _ _ len (by rw [memoryWords_length]; exact hlen),
    memoryWords_bytes _ _ _ (by omega) hin, readWithPadding_prefix _ _ _ _ hlen hin]

theorem writeWord_zero_read (mem : ByteArray) (off len : Nat) (hlen : len ≤ 32) :
    (Reasoning.Theory.writeWord mem off ⟨0⟩).readWithPadding off len = ByteArray.zeroes len := by
  by_cases hz : len = 0
  · subst len
    rw [byteArray_readWithPadding_zero, zeroes_zero (n := 0) rfl]
  have hr := writeWord_sparse_read_window mem off 0 len ⟨0⟩ (by omega) (by omega) (by omega)
  simpa only [Nat.add_zero, Nat.zero_add, zero_toByteArray_eq_zeroes32, zeroes32_extract_zeroes len hlen] using hr

theorem writeWord_zero_tail (mem : ByteArray) (off len pad : Nat)
    (hin : off + len ≤ mem.size) (hpad : pad ≤ 32) :
    (Reasoning.Theory.writeWord mem (off+len) ⟨0⟩).readWithPadding off (len+pad) =
      mem.readWithPadding off len ++ ByteArray.zeroes pad := by
  by_cases hz : len = 0
  · subst len
    simp only [Nat.add_zero, Nat.zero_add, byteArray_readWithPadding_zero, ByteArray.empty_append,
      writeWord_zero_read mem off pad hpad]
  by_cases hp : pad = 0
  · subst pad
    rw [Nat.add_zero, zeroes_zero (n := 0) rfl, ByteArray.append_empty,
      writeWord_read_below_len _ _ _ _ _ (le_refl _) hin]
  rw [byteArray_readWithPadding_split_unbounded _ off len pad (by omega) (by omega)
    (by rw [writeWord_sparse_size]; omega),
    writeWord_read_below_len _ _ _ _ _ (le_refl _) hin,
    writeWord_zero_read _ _ _ hpad]


-- LIBRARY CANDIDATE: the dynamic-byte encoder writes a length, disjoint payload words, and a zero tail.
theorem easEncodeBytesMemory_eq_sequence (src dst : UInt256) (mem : ByteArray) (len : Nat)
    (hh : memLoad src mem = UInt256.ofNat len) (hlo : 96 ≤ src.toNat)
    (hdisj : src.toNat + 32 + 32*((len+31)/32) ≤ dst.toNat)
    (hin : src.toNat + 32 + 32*((len+31)/32) ≤ mem.size)
    (hbound : dst.toNat + 64 + 32*((len+31)/32) < UInt256.size) :
    easEncodeBytesMemory src dst mem =
      Reasoning.Theory.writeWord
        (writeWordSequence (Reasoning.Theory.writeWord mem dst.toNat (UInt256.ofNat len)) (dst.toNat+32)
          (memoryWords mem (src.toNat+32) ((len+31)/32))) (dst.toNat+32+len) ⟨0⟩ := by
  have hl : len < UInt256.size := by omega
  have hs : (src + (⟨32⟩ : UInt256)).toNat = src.toNat+32 := uadd_word_ofNat_toNat src 32 (by omega)
  have hd : (dst + (⟨32⟩ : UInt256)).toNat = dst.toNat+32 := uadd_word_ofNat_toNat dst 32 (by omega)
  have hend : (UInt256.ofNat len + (dst + (⟨32⟩ : UInt256))).toNat = dst.toNat+32+len := by
    rw [u256_add_comm, uadd_word_ofNat_toNat _ _ (by rw [hd]; omega), hd]
  rw [easEncodeBytesMemory, hh, ulit_toNat' _ hl, hend,
    easCopyWords_eq_sequence _ _ _ 0 ((len+31)/32) (by rw [hs]; omega)
      (by rw [hs, hd]; omega) (by rw [hs, writeWord_sparse_size]; omega) (by rw [hd]; omega)]
  simp only [Nat.add_zero, hs, hd]
  rw [memoryWords_prefix (memoryPrefix_sparse_writeWord mem dst.toNat dst.toNat (UInt256.ofNat len) (Or.inl (le_refl _)))
    (src.toNat+32) ((len+31)/32) (by omega) hdisj hin (by omega)]


theorem writeWordSequence_covers_from (mem : ByteArray) (off : Nat) (ws : List UInt256)
    (hbase : off ≤ mem.size) : off + 32*ws.length ≤ (writeWordSequence mem off ws).size := by
  by_cases hz : ws = []
  · simpa only [hz, List.length_nil, Nat.mul_zero, Nat.add_zero, writeWordSequence] using hbase
  · exact writeWordSequence_covers mem off ws hz

theorem easEncodeBytesMemory_prefix (src dst : UInt256) (mem : ByteArray) (len : Nat)
    (hh : memLoad src mem = UInt256.ofNat len) (hlo : 96 ≤ src.toNat)
    (hdisj : src.toNat + 32 + 32*((len+31)/32) ≤ dst.toNat)
    (hin : src.toNat + 32 + 32*((len+31)/32) ≤ mem.size)
    (hbound : dst.toNat + 64 + 32*((len+31)/32) < UInt256.size) :
    MemoryPrefix mem (easEncodeBytesMemory src dst mem) dst.toNat := by
  rw [easEncodeBytesMemory_eq_sequence src dst mem len hh hlo hdisj hin hbound]
  exact (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (le_refl _))).trans
    ((writeWordSequence_prefix _ _ _ _ (by omega)).trans
      (memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (by omega))))

theorem easEncodeBytesMemory_covers (src dst : UInt256) (mem : ByteArray) (len : Nat)
    (hh : memLoad src mem = UInt256.ofNat len) (hlo : 96 ≤ src.toNat)
    (hdisj : src.toNat + 32 + 32*((len+31)/32) ≤ dst.toNat)
    (hin : src.toNat + 32 + 32*((len+31)/32) ≤ mem.size)
    (hbound : dst.toNat + 64 + 32*((len+31)/32) < UInt256.size) :
    dst.toNat + 32 + 32*((len+31)/32) ≤ (easEncodeBytesMemory src dst mem).size := by
  rw [easEncodeBytesMemory_eq_sequence src dst mem len hh hlo hdisj hin hbound, writeWord_sparse_size]
  have hc := writeWordSequence_covers_from (Reasoning.Theory.writeWord mem dst.toNat (UInt256.ofNat len))
    (dst.toNat+32) (memoryWords mem (src.toNat+32) ((len+31)/32)) (by rw [writeWord_sparse_size]; omega)
  rw [memoryWords_length] at hc
  exact le_trans hc (by omega)

theorem easEncodeBytesMemory_read (src dst : UInt256) (mem : ByteArray) (len : Nat)
    (hh : memLoad src mem = UInt256.ofNat len) (hlo : 96 ≤ src.toNat)
    (hdisj : src.toNat + 32 + 32*((len+31)/32) ≤ dst.toNat)
    (hin : src.toNat + 32 + 32*((len+31)/32) ≤ mem.size)
    (hbound : dst.toNat + 64 + 32*((len+31)/32) < UInt256.size) :
    (easEncodeBytesMemory src dst mem).readWithPadding dst.toNat (32+32*((len+31)/32)) =
      (UInt256.ofNat len).toByteArray ++ (mem.readWithPadding (src.toNat+32) len ++
        ByteArray.zeroes (32*((len+31)/32)-len)) := by
  let n := (len+31)/32
  let ws := memoryWords mem (src.toNat+32) n
  let m := writeWordSequence (Reasoning.Theory.writeWord mem dst.toNat (UInt256.ofNat len)) (dst.toNat+32) ws
  have hn : ws.length = n := memoryWords_length _ _ _
  have hc : dst.toNat+32+32*n ≤ m.size := by
    have h := writeWordSequence_covers_from (Reasoning.Theory.writeWord mem dst.toNat (UInt256.ofNat len))
      (dst.toNat+32) ws (by rw [writeWord_sparse_size]; omega)
    rw [hn] at h
    exact h
  have hr : m.readWithPadding (dst.toNat+32) len = mem.readWithPadding (src.toNat+32) len := by
    rw [show m = writeWordSequence (Reasoning.Theory.writeWord mem dst.toNat (UInt256.ofNat len)) (dst.toNat+32) ws from rfl,
      writeWordSequence_read_prefix _ _ _ len (by rw [hn]; dsimp only [n]; omega)]
    rw [show ws = memoryWords mem (src.toNat+32) n from rfl,
      memoryWords_bytes _ _ _ (by omega) hin,
      readWithPadding_prefix _ _ _ _ (by omega) hin]
  have hhead : (Reasoning.Theory.writeWord m (dst.toNat+32+len) ⟨0⟩).readWithPadding dst.toNat 32 = (UInt256.ofNat len).toByteArray := by
    rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨by omega, by omega⟩)]
    exact (writeWordSequence_read_below _ _ _ ws (by rw [writeWord_sparse_size]; omega) (le_refl _)).trans
      (writeWord_sparse_read_back _ _ _)
  rw [easEncodeBytesMemory_eq_sequence src dst mem len hh hlo hdisj hin hbound]
  change (Reasoning.Theory.writeWord m (dst.toNat+32+len) ⟨0⟩).readWithPadding dst.toNat (32+32*n) = _
  by_cases hz : n = 0
  · have hlz : len = 0 := by dsimp only [n] at hz; omega
    simp only [hz, hlz, Nat.mul_zero, Nat.add_zero, byteArray_readWithPadding_zero,
      zeroes_zero (n := 0) rfl, ByteArray.append_empty, ByteArray.empty_append]
    simpa only [hlz] using hhead
  · rw [byteArray_readWithPadding_split_unbounded _ _ 32 (32*n) (by decide) (by omega)
      (by rw [writeWord_sparse_size]; omega), hhead]
    have ht := writeWord_zero_tail m (dst.toNat+32) len (32*n-len)
      (by dsimp only [n] at hc ⊢; omega) (by dsimp only [n]; omega)
    rw [show len + (32*n-len) = 32*n by dsimp only [n]; omega, hr] at ht
    rw [ht]

end Benchmarks.EAS.EAS
