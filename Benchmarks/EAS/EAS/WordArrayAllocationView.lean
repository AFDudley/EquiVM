import Benchmarks.EAS.EAS.WordArrayAllocate
import Benchmarks.EAS.EAS.AllocateBounds
import Benchmarks.EAS.EAS.ZeroCopy
import Benchmarks.EAS.EAS.RecordPadding
import Benchmarks.EAS.EAS.MemoryArrayIndex
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: bounded word-array allocation is exact, without rounding or wrapping.
theorem allocateNext_wordArray {heap len : Nat} (hh : heap ≤ 2^64-1) (hl : len ≤ 2^64-1) :
    allocateNext heap (32+32*len) = heap+32+32*len := by
  rw [allocateNext_small hh (by omega)]
  omega

theorem wordArrayAllocationMemory_view (mem calldata : ByteArray) (heap : UInt256) (len : Nat)
    (hlo : 96 ≤ heap.toNat) (hh : heap.toNat ≤ 2^64-1) (hl : len ≤ 2^64-1) :
    let next := allocateNext heap.toNat (32+32*len)
    let final := wordArrayAllocationMemory mem calldata heap len
    MemoryPrefix mem final heap.toNat ∧ heap.toNat+32 ≤ final.size ∧
      memLoad heap final = UInt256.ofNat len ∧
      memLoad (UInt256.ofNat 64) final = UInt256.ofNat next ∧
      WordArrayMemoryView (recordPadding final next) heap (List.replicate len ⟨0⟩) next := by
  dsimp only
  let next := allocateNext heap.toNat (32+32*len)
  let header := Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat next)) heap.toNat (UInt256.ofNat len)
  let final := wordArrayAllocationMemory mem calldata heap len
  change MemoryPrefix mem final heap.toNat ∧ heap.toNat+32 ≤ final.size ∧
    memLoad heap final = UInt256.ofNat len ∧ memLoad (UInt256.ofNat 64) final = UInt256.ofNat next ∧
    WordArrayMemoryView (recordPadding final next) heap (List.replicate len ⟨0⟩) next
  have hn : next = heap.toNat+32+32*len := allocateNext_wordArray hh hl
  have hb : next < UInt256.size := by rw [hn]; change heap.toNat+32+32*len < 2^256; omega
  have hc : heap.toNat+32 ≤ header.size := by dsimp only [header]; rw [writeWord_sparse_size]; exact Nat.le_max_right _ _
  have he : final = zeroCopyMemory header (heap.toNat+32) (32*len) :=
    byteArray_write_zeroCopy calldata header calldata.size (heap.toNat+32) (32*len) (le_refl _) hc
  have hp := zeroCopyMemory_prefix header (heap.toNat+32) (32*len) hc
  have hsize : final.size = header.size := by rw [he,zeroCopyMemory_size _ _ _ hc]
  have hheader : memLoad heap header = UInt256.ofNat len :=
    mloadWordValue_of_readWithPadding (by omega) (writeWord_sparse_read_back _ _ _)
  have hlength : memLoad heap final = UInt256.ofNat len := by
    rw [he]
    exact (memLoad_of_prefix hp heap hlo (le_refl _) hc).trans hheader
  have hfree : memLoad (UInt256.ofNat 64) final = UInt256.ofNat next := by
    apply mloadWordValue_of_readWithPadding
    · change 64 < final.size
      rw [hsize]; omega
    · change final.readWithPadding 64 32 = _
      rw [he,zeroCopyMemory_read_below _ _ _ _ hc (by omega)]
      dsimp only [header]
      rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨hlo,by rw [writeWord_sparse_size]; omega⟩),
        writeWord_sparse_read_back]
  have hprefix : MemoryPrefix mem final heap.toNat := by
    rw [he]
    exact ((memoryPrefix_sparse_writeWord _ 64 _ _ (Or.inr (by decide))).trans
      (memoryPrefix_sparse_writeWord _ heap.toNat _ _ (Or.inl (le_refl _)))).trans (hp.mono (by omega))
  have hpad := recordPadding_prefix final next
  have hpadc := recordPadding_covers final next
  refine ⟨hprefix,by rw [hsize]; exact hc,hlength,hfree,hlo,?_,?_,?_,?_⟩
  · simp only [List.length_replicate]; rw [hn]
  · simp only [List.length_replicate]; omega
  · simp only [List.length_replicate]
    exact (memLoad_of_prefix hpad heap hlo (by omega) (by rw [hsize]; exact hc)).trans hlength
  · simp only [List.length_replicate]
    apply List.ext_getElem
    · rw [memoryWords_length,List.length_replicate]
    · intro i hi hj
      have hil : i < len := by simpa only [memoryWords_length] using hi
      rw [memoryWords_get _ _ _ _ hil,List.getElem_replicate]
      have hir : heap.toNat+32+32*i < UInt256.size := by omega
      apply mloadWordValue_of_readWithPadding
      · rw [ulit_toNat' _ hir]; omega
      · rw [ulit_toNat' _ hir]
        unfold recordPadding
        rw [he,hn]
        exact zeroCopyMemory_reserved_read header (heap.toNat+32) (32*len) (heap.toNat+32+32*i) _
          (by omega) hc (by omega) (by omega)

end Benchmarks.EAS.EAS
