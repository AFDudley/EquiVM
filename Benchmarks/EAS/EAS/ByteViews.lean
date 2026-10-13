import Benchmarks.EAS.EAS.WordSequence
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: the initialized prefix of a sequence of memory words.
theorem writeWordSequence_read_prefix (mem : ByteArray) (off : Nat) (ws : List UInt256)
    (len : Nat) (hlen : len ≤ 32*ws.length) :
    (writeWordSequence mem off ws).readWithPadding off len = (wordBytes ws).extract 0 len := by
  by_cases hz : len = 0
  · subst len
    rw [byteArray_readWithPadding_zero]
    exact (byteArray_extract_empty_of_le _ (by omega)).symm
  have hpos : 0 < len := by omega
  have hw : ws ≠ [] := by intro he; simp only [he, List.length_nil, Nat.mul_zero] at hlen; omega
  have hc := writeWordSequence_covers mem off ws hw
  have h := congrArg (fun b : ByteArray => b.extract 0 len) (writeWordSequence_read mem off ws)
  dsimp only at h
  rw [readWithPadding_eq_extract_unbounded _ off (32*ws.length) (by omega) hc, extract_extract_BA] at h
  rw [readWithPadding_eq_extract_unbounded _ off len hpos (by omega)]
  simpa only [Nat.add_zero, Nat.min_eq_left (by omega : off + len ≤ off + 32*ws.length)] using h

-- LIBRARY CANDIDATE: clearing the final byte preserves any prefix of the first 31 bytes.
theorem clearLowByte_prefix (word : UInt256) (len : Nat) (hlen : len ≤ 31) :
    (UInt256.land (UInt256.lnot ⟨255⟩) word).toByteArray.extract 0 len = word.toByteArray.extract 0 len := by
  have hm : (UInt256.land (UInt256.lnot ⟨255⟩) word).toByteArray =
      word.toByteArray.extract 0 31 ++ ([0] : List UInt8).toByteArray := by
    have ht := tailMask_toByteArray word ⟨31⟩ (by decide) (by decide)
    have hc : UInt256.sub (UInt256.exp ⟨256⟩ (UInt256.sub ⟨32⟩ ⟨31⟩)) ⟨1⟩ = ⟨255⟩ := by native_decide
    rw [hc] at ht
    change (UInt256.land (UInt256.lnot ⟨255⟩) word).toByteArray =
      ⟨((word.toByteArray.extract 0 31).toList ++ [0]).toArray⟩ at ht
    exact ht.trans (bytearray_append_list_eq (word.toByteArray.extract 0 31) [0]).symm
  rw [hm, extract_append_left _ _ 0 len (by rw [ByteArray.size_extract, toByteArray_size]; omega), extract_extract_BA]
  congr 1
  omega

-- LIBRARY CANDIDATE: a memory prefix preserves initialized loads.
theorem memLoad_of_prefix {before after : ByteArray} {limit : Nat} (hp : MemoryPrefix before after limit)
    (ptr : UInt256) (hlo : 96 ≤ ptr.toNat) (hhi : ptr.toNat+32 ≤ limit) (hin : ptr.toNat+32 ≤ before.size) :
    memLoad ptr after = memLoad ptr before := by
  change (if ptr.toNat ≥ after.size then (⟨0⟩ : UInt256)
    else UInt256.ofNat (fromByteArrayBigEndian (after.readWithPadding ptr.toNat 32))) =
    (if ptr.toNat ≥ before.size then (⟨0⟩ : UInt256)
    else UInt256.ofNat (fromByteArrayBigEndian (before.readWithPadding ptr.toNat 32)))
  rw [if_neg (by have hg := hp.size; omega), if_neg (by omega), hp.read _ hlo hhi hin]

end Benchmarks.EAS.EAS
