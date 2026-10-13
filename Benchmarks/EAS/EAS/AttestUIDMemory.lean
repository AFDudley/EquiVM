import Benchmarks.EAS.EAS.WordArrayAllocationView
import Benchmarks.EAS.EAS.SchemaSites
import Benchmarks.EAS.EAS.RecordUID
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def attestUIDMemory (mem calldata : ByteArray) (result heap schema : UInt256) (len : Nat) : ByteArray :=
  getSchemaCallMemory (Reasoning.Theory.writeWord (wordArrayAllocationMemory mem calldata heap len)
    (result.toNat+32) heap) (UInt256.ofNat (allocateNext heap.toNat (32+32*len))) schema

theorem attestUIDMemory_view (mem calldata : ByteArray) (result heap schema : UInt256) (len : Nat)
    (hr : 96 ≤ result.toNat) (hs : result.toNat+64 ≤ heap.toNat)
    (hh : heap.toNat ≤ 2^64-1) (hl : len ≤ 2^64-1) :
    let next := allocateNext heap.toNat (32+32*len)
    let final := attestUIDMemory mem calldata result heap schema len
    MemoryPrefix mem final (result.toNat+32) ∧ next+36 ≤ final.size ∧
      memLoad (UInt256.ofNat 64) final = UInt256.ofNat next ∧
      memLoad (result+UInt256.ofNat 32) final = heap ∧
      WordArrayMemoryView final heap (List.replicate len ⟨0⟩) next ∧
      final.readWithPadding next 36 = getSchemaPayload schema := by
  dsimp only
  let next := allocateNext heap.toNat (32+32*len)
  let arr := wordArrayAllocationMemory mem calldata heap len
  let linked := Reasoning.Theory.writeWord arr (result.toNat+32) heap
  let final := attestUIDMemory mem calldata result heap schema len
  change MemoryPrefix mem final (result.toNat+32) ∧ next+36 ≤ final.size ∧
    memLoad (UInt256.ofNat 64) final = UInt256.ofNat next ∧
    memLoad (result+UInt256.ofNat 32) final = heap ∧
    WordArrayMemoryView final heap (List.replicate len ⟨0⟩) next ∧
    final.readWithPadding next 36 = getSchemaPayload schema
  have hn : next = heap.toNat+32+32*len := allocateNext_wordArray hh hl
  have hb : next < UInt256.size := by rw [hn]; change heap.toNat+32+32*len < 2^256; omega
  have hnext : (UInt256.ofNat next).toNat = next := ulit_toNat' _ hb
  have hres : (result+UInt256.ofNat 32).toNat = result.toNat+32 := uadd_word_ofNat_toNat _ _ (by omega)
  have hefinal : final = selectorArgumentMemory linked next getSchemaSelectorWord schema := by
    simp only [final,attestUIDMemory,getSchemaCallMemory,hnext,linked,arr,next]
  obtain ⟨hpa,hca,hla,hfa,hva⟩ := wordArrayAllocationMemory_view mem calldata heap len (by omega) hh hl
  change heap.toNat+32 ≤ arr.size at hca
  have hcl : heap.toNat+32 ≤ linked.size := by dsimp only [linked]; rw [writeWord_sparse_size]; omega
  have hpl : MemoryPrefix arr linked (result.toNat+32) := memoryPrefix_sparse_writeWord _ _ _ _ (Or.inl (le_refl _))
  have hpc : MemoryPrefix linked final next := by rw [hefinal]; exact selectorArgumentMemory_prefix _ _ _ _
  have hcf : next+36 ≤ final.size := by rw [hefinal,selectorArgumentMemory_size]; exact Nat.le_max_right _ _
  have hlf : memLoad heap final = UInt256.ofNat len :=
    (memLoad_of_prefix hpc heap (by omega) (by rw [hn]; omega) hcl).trans
      ((memLoad_write_above arr (result.toNat+32) heap heap hs hca).trans hla)
  have hpointer : memLoad (result+UInt256.ofNat 32) linked = heap := by
    apply mloadWordValue_of_readWithPadding
    · rw [hres]; dsimp only [linked]; rw [writeWord_sparse_size]; omega
    · rw [hres]; exact writeWord_sparse_read_back _ _ _
  have hfree : memLoad (UInt256.ofNat 64) final = UInt256.ofNat next := by
    have h1 : memLoad (UInt256.ofNat 64) linked = UInt256.ofNat next :=
      (memLoad_write_below arr (result.toNat+32) (UInt256.ofNat 64) heap
        (by change 96 ≤ result.toNat+32; omega) (by change 96 ≤ arr.size; exact le_trans (by omega) hca)).trans hfa
    have hc : 96 ≤ linked.size := by omega
    rw [hefinal]
    unfold selectorArgumentMemory
    rw [memLoad_write_below _ (next+4) (UInt256.ofNat 64) schema
      (by change 96 ≤ next+4; rw [hn]; omega) (by change 96 ≤ (Reasoning.Theory.writeWord linked next getSchemaSelectorWord).size; rw [writeWord_sparse_size]; omega),
      memLoad_write_below linked next (UInt256.ofNat 64) getSchemaSelectorWord (by change 96 ≤ next; rw [hn]; omega) hc,h1]
  refine ⟨((hpa.mono (by omega)).trans hpl).trans (hpc.mono (by rw [hn]; omega)),hcf,hfree,?_,?_,?_⟩
  · exact (memLoad_of_prefix hpc _ (by rw [hres]; omega) (by rw [hres,hn]; omega)
      (by rw [hres]; dsimp only [linked]; rw [writeWord_sparse_size]; omega)).trans hpointer
  · refine ⟨by omega,?_,?_,?_,?_⟩
    · simp only [List.length_replicate]; rw [hn]
    · simp only [List.length_replicate]; rw [hn] at hcf; omega
    · simpa only [List.length_replicate] using hlf
    · simp only [List.length_replicate]
      apply List.ext_getElem
      · rw [memoryWords_length,List.length_replicate]
      · intro i hi hj
        have hi' : i < len := by simpa only [memoryWords_length] using hi
        rw [memoryWords_get _ _ _ _ hi',List.getElem_replicate]
        have hir : heap.toNat+32+32*i < UInt256.size := by rw [hn] at hb; omega
        apply mloadWordValue_of_readWithPadding
        · rw [ulit_toNat' _ hir]; rw [hn] at hcf; omega
        · rw [ulit_toNat' _ hir,hefinal]
          unfold selectorArgumentMemory
          rw [writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨by rw [hn]; omega,by rw [writeWord_sparse_size,hn]; omega⟩)]
          let header := Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat next)) heap.toNat (UInt256.ofNat len)
          have hheader : heap.toNat+32 ≤ header.size := by dsimp only [header]; rw [writeWord_sparse_size]; exact Nat.le_max_right _ _
          have hearr : arr = zeroCopyMemory header (heap.toNat+32) (32*len) :=
            byteArray_write_zeroCopy calldata header calldata.size (heap.toNat+32) (32*len) (le_refl _) hheader
          dsimp only [linked]
          rw [hearr,hn]
          exact zeroCopyMemory_write_reserved_read header (heap.toNat+32) (32*len) (heap.toNat+32+32*i)
            (result.toNat+32) heap getSchemaSelectorWord (by omega) hheader (by omega) (by omega)
  · have h := getSchemaCallMemory_read linked (UInt256.ofNat next) schema
    simpa only [hnext] using h

end Benchmarks.EAS.EAS
