import Benchmarks.EAS.EAS.RecordArraySet
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem AttestationArrayMemoryView.write_disjoint {mem : ByteArray} {array : UInt256}
    {ats : List AttestationRecord} {limit : Nat}
    (h : AttestationArrayMemoryView mem array ats limit) (dst : Nat) (word : UInt256) (hb : limit < UInt256.size)
    (ht : array.toNat+32+32*ats.length ≤ dst ∨ dst+32 ≤ array.toNat)
    (hsafe : ∀ j (hj : j < ats.length), ∃ p d,
      memLoad (UInt256.ofNat (array.toNat+32+32*j)) mem = p ∧
      AttestationMemoryView mem p d ats[j] ∧ p.toNat+320 ≤ limit ∧
      d.toNat+32+32*((ats[j].data.size+31)/32) ≤ limit ∧
      (p.toNat+320 ≤ dst ∨ dst+32 ≤ p.toNat) ∧
      (d.toNat+32+32*((ats[j].data.size+31)/32) ≤ dst ∨ dst+32 ≤ d.toNat)) :
    AttestationArrayMemoryView (Reasoning.Theory.writeWord mem dst word) array ats limit := by
  have hspan := h.span
  have hc := h.covered
  have hload (ptr : UInt256) (hlo : array.toNat ≤ ptr.toNat) (hhi : ptr.toNat+32 ≤ array.toNat+32+32*ats.length) :
      memLoad ptr (Reasoning.Theory.writeWord mem dst word) = memLoad ptr mem := by
    rcases ht with ht | ht
    · exact memLoad_write_below _ _ _ _ (by omega) (by omega)
    · exact memLoad_write_above _ _ _ _ (by omega) (by omega)
  refine ⟨h.low,h.span,?_,(hload array (le_refl _) (by omega)).trans h.length,?_⟩
  · rw [writeWord_sparse_size]; omega
  · intro j hj
    obtain ⟨p,d,hp,hv,hps,hpd,hsp,hdp⟩ := hsafe j hj
    refine ⟨p,d,?_,hv.write_disjoint dst word (by omega) hsp hdp,hps,hpd⟩
    have hn : (UInt256.ofNat (array.toNat+32+32*j)).toNat = array.toNat+32+32*j := ulit_toNat' _ (by omega)
    exact (hload _ (by rw [hn]; omega) (by rw [hn]; omega)).trans hp

end Benchmarks.EAS.EAS
