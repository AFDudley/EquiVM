import Benchmarks.EAS.EAS.CopyEncodeViews
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: copying from beyond the source clears only the covered destination bytes.
def zeroCopyMemory (mem : ByteArray) (off len : Nat) : ByteArray :=
  mem.extract 0 off ++ ByteArray.zeroes (min len (mem.size-off)) ++
    mem.extract (off+min len (mem.size-off)) mem.size

theorem byteArray_write_zeroCopy (src mem : ByteArray) (srcOff off len : Nat)
    (hsrc : src.size ≤ srcOff) (hin : off ≤ mem.size) :
    src.write srcOff mem off len = zeroCopyMemory mem off len := by
  by_cases hz : len = 0
  · subst len
    simp only [byteArray_write_len_zero,zeroCopyMemory,Nat.zero_min,zeroes_zero (n := 0) rfl,
      ByteArray.append_empty,Nat.add_zero,ByteArray.extract_append_extract,Nat.zero_min,Nat.max_eq_right hin]
    exact (byteArray_extract_self mem).symm
  · unfold ByteArray.write
    rw [if_neg hz,if_pos hsrc,Nat.min_eq_left hin]
    apply ByteArray.ext
    simp only [zeroCopyMemory,ByteArray.data_copySlice,ByteArray.data_append,ByteArray.data_extract,Nat.zero_add]
    rw [Array.extract_eq_self_of_le (show (ByteArray.zeroes (min len (mem.size-off))).data.size ≤ min len (mem.size-off) by
      exact le_of_eq (ByteArray_zeroes_size _))]
    simp only [show (ByteArray.zeroes (min len (mem.size-off))).data.size = min len (mem.size-off) from ByteArray_zeroes_size _,
      Nat.sub_zero,Nat.min_self]
    congr 1

theorem zeroCopyMemory_size (mem : ByteArray) (off len : Nat) (hin : off ≤ mem.size) :
    (zeroCopyMemory mem off len).size = mem.size := by
  simp only [zeroCopyMemory,ByteArray.size_append,ByteArray.size_extract,ByteArray_zeroes_size]
  omega

theorem zeroCopyMemory_read_below (mem : ByteArray) (off len read : Nat)
    (hin : off ≤ mem.size) (hlo : read+32 ≤ off) :
    (zeroCopyMemory mem off len).readWithPadding read 32 = mem.readWithPadding read 32 := by
  rw [readWithPadding_eq_extract _ read (by rw [zeroCopyMemory_size _ _ _ hin]; omega)]
  unfold zeroCopyMemory
  rw [extract_append_left _ _ _ _ (by rw [ByteArray.size_append,ByteArray.size_extract,ByteArray_zeroes_size]; omega),
    extract_append_left _ _ _ _ (by rw [ByteArray.size_extract]; omega),extract_extract_BA]
  simpa only [Nat.zero_add,Nat.min_eq_left hlo] using (readWithPadding_eq_extract mem read (by omega)).symm

theorem zeroCopyMemory_prefix (mem : ByteArray) (off len : Nat) (hin : off ≤ mem.size) :
    MemoryPrefix mem (zeroCopyMemory mem off len) off :=
  ⟨(zeroCopyMemory_size mem off len hin).ge,fun read _ hlo _ => zeroCopyMemory_read_below mem off len read hin hlo⟩

-- LIBRARY CANDIDATE: zero blocks concatenate and have zero-valued subwindows.
theorem byteArray_zeroes_append (n m : Nat) :
    ByteArray.zeroes n ++ ByteArray.zeroes m = ByteArray.zeroes (n+m) := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [ByteArray.data_append,Array.toList_append,byteArray_zeroes_toList,List.replicate_add]

theorem byteArray_zeroes_extract (n off len : Nat) (hin : off+len ≤ n) :
    (ByteArray.zeroes n).extract off (off+len) = ByteArray.zeroes len := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [ByteArray.data_extract,Array.toList_extract,byteArray_zeroes_toList,List.extract_eq_take_drop,
    List.drop_replicate,List.take_replicate]
  congr 1
  omega

theorem zeroBlock_read (pre post : ByteArray) (len read : Nat)
    (hlo : pre.size ≤ read) (hhi : read+32 ≤ pre.size+len) :
    (pre ++ ByteArray.zeroes len ++ post).readWithPadding read 32 = (⟨0⟩ : UInt256).toByteArray := by
  rw [readWithPadding_eq_extract _ read (by rw [ByteArray.size_append,ByteArray.size_append,ByteArray_zeroes_size]; omega),
    extract_append_left _ _ _ _ (by rw [ByteArray.size_append,ByteArray_zeroes_size]; exact hhi),
    extract_append_right_window _ _ _ _ hlo]
  rw [show read+32-pre.size = read-pre.size+32 by omega,
    byteArray_zeroes_extract _ _ _ (by omega),zero_toByteArray_eq_zeroes32]

theorem zeroCopyMemory_read (mem : ByteArray) (off len read : Nat)
    (hlo : off ≤ read) (hhi : read+32 ≤ off+len) (hin : read+32 ≤ mem.size) :
    (zeroCopyMemory mem off len).readWithPadding read 32 = (⟨0⟩ : UInt256).toByteArray := by
  apply zeroBlock_read
  · rw [ByteArray.size_extract]; omega
  · rw [ByteArray.size_extract]; omega

-- LIBRARY CANDIDATE: an in-bounds write commutes with appending an untouched suffix.
theorem writeWord_append_suffix (pre post : ByteArray) (off : Nat) (word : UInt256)
    (hin : off+32 ≤ pre.size) :
    Reasoning.Theory.writeWord (pre++post) off word = Reasoning.Theory.writeWord pre off word ++ post := by
  have ht : (pre++post).extract (off+32) (pre.size+post.size) = pre.extract (off+32) pre.size ++ post := by
    rw [ByteArray.extract_append,show off+32-pre.size = 0 by omega,
      show pre.size+post.size-pre.size = post.size by omega,byteArray_extract_self]
    congr 1
    apply ByteArray.ext
    rw [ByteArray.data_extract,ByteArray.data_extract,Array.extract_eq_extract_right]
    change min (pre.size+post.size-(off+32)) (pre.size-(off+32)) = min (pre.size-(off+32)) (pre.size-(off+32))
    omega
  unfold Reasoning.Theory.writeWord
  rw [write_eq_gen _ _ _ _ (by decide) (by rw [toByteArray_size]) (by rw [ByteArray.size_append]; omega),
    write_eq_gen _ _ _ _ (by decide) (by rw [toByteArray_size]) hin,
    extract_append_left _ _ _ _ (by omega),ByteArray.size_append,ht]
  simp only [ByteArray.append_assoc]

-- LIBRARY CANDIDATE: reserving a later word makes an implicitly zero-filled window explicit.
theorem zeroCopyMemory_write_reserved_read (mem : ByteArray) (off len read dst : Nat) (next word : UInt256)
    (hbase : dst+32 ≤ off) (hstart : off ≤ mem.size) (hlo : off ≤ read) (hhi : read+32 ≤ off+len) :
    (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord (zeroCopyMemory mem off len) dst next)
      (off+len) word).readWithPadding read 32 = (⟨0⟩ : UInt256).toByteArray := by
  by_cases hin : read+32 ≤ mem.size
  · rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨hhi,by
      rw [writeWord_sparse_size,zeroCopyMemory_size _ _ _ hstart]; omega⟩),
      writeWord_sparse_read_preserved _ _ _ _ (Or.inr ⟨by omega,by rw [zeroCopyMemory_size _ _ _ hstart]; exact hin⟩)]
    exact zeroCopyMemory_read mem off len read hlo hhi hin
  · have hg : mem.size < off+len := by omega
    have hclear : zeroCopyMemory mem off len = mem.extract 0 off ++ ByteArray.zeroes (mem.size-off) := by
      unfold zeroCopyMemory
      rw [Nat.min_eq_right (by omega),show off+(mem.size-off) = mem.size by omega,
        byteArray_extract_empty_of_le _ (le_refl _),ByteArray.append_empty]
    rw [hclear,writeWord_append_suffix _ _ dst next (by rw [ByteArray.size_extract]; omega)]
    let pre := Reasoning.Theory.writeWord (mem.extract 0 off) dst next
    have hp : pre.size = off := by
      dsimp only [pre]
      rw [writeWord_sparse_size,ByteArray.size_extract]
      omega
    change (Reasoning.Theory.writeWord (pre++ByteArray.zeroes (mem.size-off)) (off+len) word).readWithPadding read 32 = _
    rw [writeWord_sparse_eq _ _ _ (by rw [ByteArray.size_append,hp,ByteArray_zeroes_size]; omega),
      ByteArray.size_append,hp,ByteArray_zeroes_size,
      show off+len-(off+(mem.size-off)) = off+len-mem.size by omega,
      (ByteArray.append_assoc (a := pre) (b := ByteArray.zeroes (mem.size-off)) (c := ByteArray.zeroes (off+len-mem.size))),
      byteArray_zeroes_append,show mem.size-off+(off+len-mem.size) = len by omega]
    exact zeroBlock_read pre _ len read (by rw [hp]; exact hlo) (by rw [hp]; exact hhi)


theorem zeroCopyMemory_reserved_read (mem : ByteArray) (off len read : Nat) (next : UInt256)
    (hbase : 96 ≤ off) (hstart : off ≤ mem.size) (hlo : off ≤ read) (hhi : read+32 ≤ off+len) :
    (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord (zeroCopyMemory mem off len) 64 next)
      (off+len) ⟨0⟩).readWithPadding read 32 = (⟨0⟩ : UInt256).toByteArray :=
  zeroCopyMemory_write_reserved_read mem off len read 64 next ⟨0⟩ hbase hstart hlo hhi

end Benchmarks.EAS.EAS
