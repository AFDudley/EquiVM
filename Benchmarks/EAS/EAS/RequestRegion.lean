import Benchmarks.EAS.EAS.RequestArrayMemory
import Benchmarks.EAS.EAS.RecordDisjoint
import Benchmarks.EAS.EAS.RecordArrayViews
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem AttestationRequestMemoryView.write_below {mem : ByteArray} {ptr dataPtr : UInt256}
    {r : AttestationRequestRecord} (h : AttestationRequestMemoryView mem ptr dataPtr r)
    (dst : Nat) (word : UInt256) (hb : ptr.toNat+192 < UInt256.size)
    (hs : dst+32 ≤ ptr.toNat) (hd : dst+32 ≤ dataPtr.toNat) :
    AttestationRequestMemoryView (Reasoning.Theory.writeWord mem dst word) ptr dataPtr r := by
  have hc := h.covered
  have hdc := h.dataCovered
  have hoff (n : Nat) (hn : n ≤ 160) :
      memLoad (ptr+UInt256.ofNat n) (Reasoning.Theory.writeWord mem dst word) = memLoad (ptr+UInt256.ofNat n) mem := by
    have he : (ptr+UInt256.ofNat n).toNat = ptr.toNat+n := uadd_word_ofNat_toNat _ _ (by omega)
    exact memLoad_write_above _ _ _ _ (by rw [he]; omega) (by rw [he]; omega)
  have h0 := memLoad_write_above mem dst ptr word hs (by omega)
  refine ⟨h.low,h.dataLow,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [writeWord_sparse_size]; omega
  · rw [writeWord_sparse_size]; omega
  · rw [h0]; exact h.recipient
  · rw [hoff 32 (by decide)]; exact h.expiration
  · rw [hoff 64 (by decide)]; exact h.revocable
  · exact (hoff 96 (by decide)).trans h.refUID
  · exact (hoff 128 (by decide)).trans h.pointer
  · exact (hoff 160 (by decide)).trans h.value
  · exact (memLoad_write_above _ _ _ _ hd (by omega)).trans h.length
  · exact (writeWord_read_above_len _ _ _ _ _ (by omega) (by omega)).trans h.payload

-- Lower bounds keep decoded request objects clear of the compiler's reserved words.
structure AttestationRequestArrayRegion (mem : ByteArray) (array : UInt256)
    (rs : List AttestationRequestRecord) (lower upper : Nat) : Prop where
  view : AttestationRequestArrayMemoryView mem array rs upper
  arrayLow : lower ≤ array.toNat
  objectsLow : ∀ i (hi : i < rs.length),
    lower ≤ (memLoad (UInt256.ofNat (array.toNat+32+32*i)) mem).toNat ∧
    lower ≤ (memLoad ((memLoad (UInt256.ofNat (array.toNat+32+32*i)) mem)+UInt256.ofNat 128) mem).toNat

theorem AttestationRequestArrayRegion.write_below {mem : ByteArray} {array : UInt256}
    {rs : List AttestationRequestRecord} {lower upper : Nat}
    (h : AttestationRequestArrayRegion mem array rs lower upper) (dst : Nat) (word : UInt256)
    (hd : dst+32 ≤ lower) (hb : upper < UInt256.size) :
    AttestationRequestArrayRegion (Reasoning.Theory.writeWord mem dst word) array rs lower upper := by
  have hs := h.view.span
  have hc := h.view.covered
  have ha := h.arrayLow
  have hslot (i : Nat) (hi : i < rs.length) :
      memLoad (UInt256.ofNat (array.toNat+32+32*i)) (Reasoning.Theory.writeWord mem dst word) =
      memLoad (UInt256.ofNat (array.toNat+32+32*i)) mem := by
    have hn : (UInt256.ofNat (array.toNat+32+32*i)).toNat = array.toNat+32+32*i := ulit_toNat' _ (by omega)
    exact memLoad_write_above _ _ _ _ (by rw [hn]; omega) (by rw [hn]; omega)
  have hrecord (i : Nat) (hi : i < rs.length) : ∃ ptr dp,
      memLoad (UInt256.ofNat (array.toNat+32+32*i)) (Reasoning.Theory.writeWord mem dst word) = ptr ∧
      AttestationRequestMemoryView (Reasoning.Theory.writeWord mem dst word) ptr dp rs[i] ∧
      ptr.toNat+192 ≤ upper ∧ dp.toNat+32+32*((rs[i].data.size+31)/32) ≤ upper ∧ lower ≤ ptr.toNat ∧ lower ≤ dp.toNat := by
    obtain ⟨ptr,dp,hp,hv,he,hde⟩ := h.view.requests i hi
    have hl := h.objectsLow i hi
    rw [hp,hv.pointer] at hl
    exact ⟨ptr,dp,(hslot i hi).trans hp,hv.write_below dst word (by omega) (by omega) (by omega),he,hde,hl⟩
  refine ⟨⟨h.view.low,h.view.span,?_,?_,?_⟩,h.arrayLow,?_⟩
  · rw [writeWord_sparse_size]; omega
  · exact (memLoad_write_above _ _ _ _ (by omega) (by omega)).trans h.view.length
  · intro i hi
    obtain ⟨ptr,dp,hp,hv,he,hd,_,_⟩ := hrecord i hi
    exact ⟨ptr,dp,hp,hv,he,hd⟩
  · intro i hi
    obtain ⟨ptr,dp,hp,hv,_,_,hl,hdl⟩ := hrecord i hi
    rw [hp,hv.pointer]
    exact ⟨hl,hdl⟩

theorem AttestationRequestArrayRegion.preserve {before after : ByteArray} {array : UInt256}
    {rs : List AttestationRequestRecord} {lower upper : Nat}
    (h : AttestationRequestArrayRegion before array rs lower upper)
    (hp : MemoryPrefix before after upper) (hb : upper < UInt256.size) :
    AttestationRequestArrayRegion after array rs lower upper := by
  have hv := h.view.preserve hp hb
  refine ⟨hv,h.arrayLow,?_⟩
  intro i hi
  obtain ⟨ptr,dp,hptr,hv0,he,hd⟩ := h.view.requests i hi
  have hn : (UInt256.ofNat (array.toNat+32+32*i)).toNat = array.toNat+32+32*i :=
    ulit_toNat' _ (by have := h.view.span; omega)
  have hslot := memLoad_of_prefix hp (UInt256.ofNat (array.toNat+32+32*i))
    (by rw [hn]; have := h.view.low; omega) (by rw [hn]; have := h.view.span; omega)
    (by rw [hn]; have := h.view.covered; omega)
  have hlow := h.objectsLow i hi
  rw [hptr,hv0.pointer] at hlow
  rw [hslot,hptr,(hv0.preserve hp he hd hb).pointer]
  exact hlow

end Benchmarks.EAS.EAS
