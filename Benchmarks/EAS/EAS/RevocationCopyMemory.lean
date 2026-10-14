import Benchmarks.EAS.EAS.PointerTableMemory
import Benchmarks.EAS.EAS.CopyRevocationArrayControl
import Benchmarks.EAS.EAS.RevocationArrayDecode
import Benchmarks.EAS.EAS.RevocationRequestMemory
import Benchmarks.EAS.EAS.RecordUID
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem RevocationRequestMemoryView.write_below {mem : ByteArray} {ptr : UInt256}
    {r : RevocationRequestRecord} (h : RevocationRequestMemoryView mem ptr r)
    (dst : Nat) (word : UInt256) (hb : ptr.toNat+64 < UInt256.size) (hs : dst+32 ≤ ptr.toNat) :
    RevocationRequestMemoryView (Reasoning.Theory.writeWord mem dst word) ptr r := by
  have hc := h.covered
  have hoff : (ptr+UInt256.ofNat 32).toNat = ptr.toNat+32 := uadd_word_ofNat_toNat _ _ (by omega)
  exact ⟨h.low,by rw [writeWord_sparse_size]; omega,
    (memLoad_write_above _ _ _ _ hs (by omega)).trans h.uid,
    (memLoad_write_above _ _ _ _ (by rw [hoff]; omega) (by rw [hoff]; omega)).trans h.value⟩

def revocationRecordMemory (mem : ByteArray) (heap : UInt256) (r : RevocationRequestRecord) : ByteArray :=
  writeWordSequence (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (heap.toNat+64))) heap.toNat [r.uid,r.value]

theorem revocationRecordMemory_facts (mem : ByteArray) (heap : UInt256) (r : RevocationRequestRecord)
    (hlo : 96 ≤ heap.toNat) (hb : heap.toNat+64 < UInt256.size) :
    MemoryPrefix mem (revocationRecordMemory mem heap r) heap.toNat ∧
    RevocationRequestMemoryView (revocationRecordMemory mem heap r) heap r ∧
    memLoad (UInt256.ofNat 64) (revocationRecordMemory mem heap r) = UInt256.ofNat (heap.toNat+64) := by
  have hc : heap.toNat+64 ≤ (revocationRecordMemory mem heap r).size := by
    have h := writeWordSequence_covers (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (heap.toNat+64)))
      heap.toNat [r.uid,r.value] (by intro h; cases h)
    exact h
  have hget (i : Nat) (hi : i < 2) :
      memLoad (UInt256.ofNat (heap.toNat+32*i)) (revocationRecordMemory mem heap r) = [r.uid,r.value][i] :=
    writeWordSequence_load_index _ _ _ _ hi (by omega)
  refine ⟨?_,⟨hlo,hc,?_,?_⟩,writeWordSequence_setFree_load64 _ _ _ _ hlo⟩
  · exact (memoryPrefix_sparse_writeWord mem 64 heap.toNat _ (Or.inr (by decide))).trans
      (writeWordSequence_prefix _ heap.toNat heap.toNat _ (le_refl _))
  · simpa only [Nat.mul_zero,Nat.add_zero,u256_ofNat_toNat,List.getElem_cons_zero] using hget 0 (by decide)
  · have hword : heap+UInt256.ofNat 32 = UInt256.ofNat (heap.toNat+32) := by
      apply u256_inj
      rw [uadd_word_ofNat_toNat _ _ (by omega),ulit_toNat' _ (by omega)]
    rw [hword]
    exact hget 1 (by decide)

def RevocationCopyRegion (mem : ByteArray) (ptr : UInt256) (r : RevocationRequestRecord) (lower heap : Nat) : Prop :=
  RevocationRequestMemoryView mem ptr r ∧ ptr.toNat+64 ≤ heap ∧ lower ≤ ptr.toNat
abbrev CopyRevocationArrayMemory := PointerTablePrefix RevocationCopyRegion

theorem CopyRevocationArrayMemory.finish {mem : ByteArray} {array : UInt256}
    {rs : List RevocationRequestRecord} {heap : Nat}
    (h : CopyRevocationArrayMemory mem array rs rs.length heap) :
    RevocationRequestArrayMemoryView mem array rs heap := by
  refine ⟨h.low,h.span,h.covered,h.length,?_⟩
  intro i hi
  obtain ⟨ptr,hp,hv,he,hl⟩ := h.elements i hi
  exact ⟨ptr,hp,hv,he⟩

theorem revocationArrayCopyMemory_eq {cd : ByteArray} {src dst heap : UInt256} (mem : ByteArray)
    (hs : src.toNat+32 < UInt256.size) (hh : heap.toNat+32 < UInt256.size) :
    revocationArrayCopyMemory mem cd src dst heap =
      Reasoning.Theory.writeWord (revocationRecordMemory mem heap (revocationDataRecord cd src.toNat)) dst.toNat heap := by
  simp only [revocationArrayCopyMemory,revocationRecordMemory,writeWordSequence,revocationDataRecord,
    uadd_word_ofNat_toNat _ _ hs,uadd_word_ofNat_toNat _ _ hh]

theorem revocationArrayCopyMemory_step {mem : ByteArray} {array heap : UInt256}
    {cd : ByteArray} {src : UInt256} {rs : List RevocationRequestRecord} {i : Nat}
    (h : CopyRevocationArrayMemory mem array rs i heap.toNat) (hi : i < rs.length)
    (hh : heap.toNat+64 < UInt256.size) (hs : src.toNat+32 < UInt256.size)
    (hr : revocationDataRecord cd src.toNat = rs[i]) :
    let final := revocationArrayCopyMemory mem cd src (UInt256.ofNat (array.toNat+32+32*i)) heap
    MemoryPrefix mem final array.toNat ∧ CopyRevocationArrayMemory final array rs (i+1) (heap.toNat+64) ∧
    memLoad (UInt256.ofNat 64) final = UInt256.ofNat (heap.toNat+64) := by
  have hlo : 96 ≤ heap.toNat := by have := h.low; have := h.span; omega
  have hslot : (UInt256.ofNat (array.toNat+32+32*i)).toNat = array.toNat+32+32*i :=
    ulit_toNat' _ (by have := h.span; omega)
  dsimp only
  rw [revocationArrayCopyMemory_eq mem hs (by omega),hslot,hr]
  let copied := revocationRecordMemory mem heap rs[i]
  have hc := revocationRecordMemory_facts mem heap rs[i] hlo hh
  have hp : MemoryPrefix mem copied heap.toNat := hc.1
  have hnew : CopyRevocationArrayMemory copied array rs i (heap.toNat+64) := by
    apply PointerTablePrefix.preserve h hp (by omega) hh
    intro ptr r hv
    exact ⟨hv.1.preserve hp hv.2.1 (by omega),by have := hv.2.1; omega,hv.2.2⟩
  have hm : CopyRevocationArrayMemory (Reasoning.Theory.writeWord copied (array.toNat+32+32*i) heap)
      array rs (i+1) (heap.toNat+64) := by
    apply PointerTablePrefix.set hnew hi ⟨hc.2.1,le_refl _,h.span⟩ hh
    intro ptr r hv
    exact ⟨hv.1.write_below _ heap (by have := hv.2.1; omega) (by have := hv.2.2; omega),hv.2⟩
  refine ⟨?_,hm,?_⟩
  · exact (hp.mono (by have := h.span; omega)).trans
      (memoryPrefix_sparse_writeWord copied _ array.toNat heap (Or.inl (by omega)))
  · exact (memLoad_write_below copied _ _ heap (by change 96 ≤ _; have := h.low; omega)
      (by change 96 ≤ (revocationRecordMemory mem heap rs[i]).size; have := hc.2.1.covered; omega)).trans hc.2.2

end Benchmarks.EAS.EAS
