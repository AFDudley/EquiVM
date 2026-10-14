import Benchmarks.EAS.EAS.PointerTableMemory
import Benchmarks.EAS.EAS.SignatureCopy
import Benchmarks.EAS.EAS.DelegatedAttestPrepareMemory
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

structure SignatureArrayMemoryView (mem : ByteArray) (array : UInt256) (ss : List SignatureRecord) (heap : Nat) : Prop where
  low : 96 ≤ array.toNat
  span : array.toNat+32+32*ss.length ≤ heap
  covered : array.toNat+32+32*ss.length ≤ mem.size
  length : memLoad array mem = UInt256.ofNat ss.length
  elements : ∀ i (hi : i<ss.length), ∃ ptr,
    memLoad (UInt256.ofNat (array.toNat+32+32*i)) mem = ptr ∧ SignatureMemoryView mem ptr ss[i] ∧ ptr.toNat+96 ≤ heap

def SignatureCopyRegion (mem : ByteArray) (ptr : UInt256) (s : SignatureRecord) (lower heap : Nat) : Prop :=
  SignatureMemoryView mem ptr s ∧ ptr.toNat+96 ≤ heap ∧ lower ≤ ptr.toNat
abbrev CopySignatureArrayMemory := PointerTablePrefix SignatureCopyRegion

theorem CopySignatureArrayMemory.finish {mem : ByteArray} {array : UInt256} {ss : List SignatureRecord} {heap : Nat}
    (h : CopySignatureArrayMemory mem array ss ss.length heap) : SignatureArrayMemoryView mem array ss heap := by
  refine ⟨h.low,h.span,h.covered,h.length,?_⟩
  intro i hi
  obtain ⟨ptr,hp,hv,he,hl⟩ := h.elements i hi
  exact ⟨ptr,hp,hv,he⟩

def signatureArrayCopyMemory (mem : ByteArray) (dst heap : UInt256) (s : SignatureRecord) : ByteArray :=
  writeWord (signatureCopyMemory mem heap s) dst.toNat heap

theorem signatureArrayCopyMemory_step {mem : ByteArray} {array heap : UInt256} {ss : List SignatureRecord} {i : Nat}
    (h : CopySignatureArrayMemory mem array ss i heap.toNat) (hi : i<ss.length)
    (hh : heap.toNat+96 < UInt256.size) (hclean : signatureClean ss[i]) :
    let final := signatureArrayCopyMemory mem (UInt256.ofNat (array.toNat+32+32*i)) heap ss[i]
    MemoryPrefix mem final array.toNat ∧ CopySignatureArrayMemory final array ss (i+1) (heap.toNat+96) ∧
    memLoad (UInt256.ofNat 64) final = UInt256.ofNat (heap.toNat+96) := by
  have hlo : 96 ≤ heap.toNat := by have := h.low; have := h.span; omega
  have hslot : (UInt256.ofNat (array.toNat+32+32*i)).toNat = array.toNat+32+32*i := ulit_toNat' _ (by have := h.span; omega)
  dsimp only
  rw [signatureArrayCopyMemory,hslot]
  let copied := signatureCopyMemory mem heap ss[i]
  have hc := signatureCopyMemory_facts mem heap ss[i] hlo hh hclean
  have hp : MemoryPrefix mem copied heap.toNat := hc.1
  have hnew : CopySignatureArrayMemory copied array ss i (heap.toNat+96) := by
    apply PointerTablePrefix.preserve h hp (by omega) hh
    intro ptr s hv
    exact ⟨hv.1.preserve hp hv.2.1 (by omega),by have := hv.2.1; omega,hv.2.2⟩
  have hm : CopySignatureArrayMemory (writeWord copied (array.toNat+32+32*i) heap) array ss (i+1) (heap.toNat+96) := by
    apply PointerTablePrefix.set hnew hi ⟨hc.2.1,le_refl _,h.span⟩ hh
    intro ptr s hv
    exact ⟨hv.1.write_below _ heap (by have := hv.2.1; omega) (by have := hv.2.2; omega),hv.2⟩
  refine ⟨?_,hm,?_⟩
  · exact (hp.mono (by have := h.span; omega)).trans
      (memoryPrefix_sparse_writeWord copied _ array.toNat heap (Or.inl (by omega)))
  · exact (memLoad_write_below copied _ _ heap (by change 96 ≤ _; have := h.low; omega)
      (by change 96 ≤ (signatureCopyMemory mem heap ss[i]).size; have := hc.2.1.covered; omega)).trans hc.2.2

end Benchmarks.EAS.EAS
