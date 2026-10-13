import Benchmarks.EAS.EAS.RecordDisjoint
import Benchmarks.EAS.EAS.RecordArrayMemory
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem AttestationArrayMemoryView.set {mem : ByteArray} {array src dataPtr : UInt256}
    {ats : List AttestationRecord} {a : AttestationRecord} {limit i : Nat}
    (h : AttestationArrayMemoryView mem array ats limit) (hi : i < ats.length)
    (ha : AttestationMemoryView mem src dataPtr a) (hsrc : src.toNat+320 ≤ limit)
    (hdata : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ limit) (hb : limit < UInt256.size)
    (hsafe : ∀ j (hj : j < ats.length), ∃ p d,
      memLoad (UInt256.ofNat (array.toNat+32+32*j)) mem = p ∧
      AttestationMemoryView mem p d ats[j] ∧ p.toNat+320 ≤ limit ∧
      d.toNat+32+32*((ats[j].data.size+31)/32) ≤ limit ∧
      (p.toNat+320 ≤ array.toNat+32+32*i ∨ array.toNat+64+32*i ≤ p.toNat) ∧
      (d.toNat+32+32*((ats[j].data.size+31)/32) ≤ array.toNat+32+32*i ∨ array.toNat+64+32*i ≤ d.toNat))
    (hsa : src.toNat+320 ≤ array.toNat+32+32*i ∨ array.toNat+64+32*i ≤ src.toNat)
    (hda : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ array.toNat+32+32*i ∨ array.toNat+64+32*i ≤ dataPtr.toNat) :
    AttestationArrayMemoryView (Reasoning.Theory.writeWord mem (array.toNat+32+32*i) src) array (ats.set i a) limit := by
  have hs := h.span
  have hc := h.covered
  have hn (j : Nat) (hj : j < ats.length) : (UInt256.ofNat (array.toNat+32+32*j)).toNat = array.toNat+32+32*j :=
    ulit_toNat' _ (by omega)
  refine ⟨h.low,?_,?_,?_,?_⟩
  · simpa only [List.length_set] using h.span
  · rw [List.length_set,writeWord_sparse_size]; omega
  · rw [List.length_set]
    exact (memLoad_write_below _ _ _ _ (by omega) (by omega)).trans h.length
  · intro j hj
    have hj0 : j < ats.length := by simpa only [List.length_set] using hj
    by_cases he : i = j
    · subst j
      simp only [List.getElem_set_self]
      refine ⟨src,dataPtr,?_,ha.write_disjoint _ src (by omega) (by omega) (by omega),hsrc,hdata⟩
      exact mloadWordValue_of_readWithPadding (by rw [hn i hi,writeWord_sparse_size]; omega)
        (by rw [hn i hi]; exact writeWord_sparse_read_back _ _ _)
    · rw [List.getElem_set_ne he]
      obtain ⟨p,d,hp,hv,hps,hpd,hsp,hdp⟩ := hsafe j hj0
      refine ⟨p,d,?_,hv.write_disjoint _ src (by omega) (by omega) (by omega),hps,hpd⟩
      rcases lt_or_gt_of_ne he with hij | hji
      · exact (memLoad_write_above _ _ _ _ (by rw [hn j hj0]; omega) (by rw [hn j hj0]; omega)).trans hp
      · exact (memLoad_write_below _ _ _ _ (by rw [hn j hj0]; omega) (by rw [hn j hj0]; omega)).trans hp

end Benchmarks.EAS.EAS
