import Benchmarks.EAS.EAS.DelegatedAttestDecode
import Benchmarks.EAS.EAS.DelegatedAttestMemory
import Benchmarks.EAS.EAS.DelegatedRevokePrepareMemory
import Benchmarks.EAS.EAS.SignatureCopy
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: preserve a signature when writing below its record.
theorem SignatureMemoryView.write_below {mem : ByteArray} {ptr : UInt256} {s : SignatureRecord}
    (h : SignatureMemoryView mem ptr s) (dst : Nat) (w : UInt256)
    (hb : ptr.toNat+96 < UInt256.size) (hd : dst+32 ≤ ptr.toNat) :
    SignatureMemoryView (Reasoning.Theory.writeWord mem dst w) ptr s := by
  have hc := h.covered
  have keep (n : Nat) (hn : n ≤ 64) :
      memLoad (ptr+UInt256.ofNat n) (Reasoning.Theory.writeWord mem dst w) = memLoad (ptr+UInt256.ofNat n) mem := by
    have ho := uadd_word_ofNat_toNat ptr n (by omega : ptr.toNat+n < UInt256.size)
    exact memLoad_write_above _ _ _ _ (by rw [ho]; omega) (by rw [ho]; omega)
  refine ⟨h.low,by rw [writeWord_sparse_size]; omega,?_,(keep 32 (by decide)).trans h.r,(keep 64 (by decide)).trans h.s⟩
  rw [memLoad_write_above _ _ _ _ hd (by omega)]
  exact h.v

def delegatedAttestSchemaMemory (cd : ByteArray) (root : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (Reasoning.Theory.writeWord attestPublicInitialMemory 64 (UInt256.ofNat 352))
    224 (calldataWord cd root.toNat)
def delegatedAttestCopiedMemory (cd : ByteArray) (root : UInt256) : ByteArray :=
  requestCopyMemory (delegatedAttestSchemaMemory cd root) cd (delegatedAttestData cd root) (UInt256.ofNat 352)
def delegatedAttestCopyHeap (cd : ByteArray) (root : UInt256) : Nat :=
  copyRequestNext 352 (delegatedAttestRecord cd root).data.data.size
def delegatedAttestLinkedMemory (cd : ByteArray) (root : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (delegatedAttestCopiedMemory cd root) 256 (UInt256.ofNat 352)
def delegatedAttestSignatureMemory (cd : ByteArray) (root : UInt256) : ByteArray :=
  signatureCopyMemory (delegatedAttestLinkedMemory cd root) (UInt256.ofNat (delegatedAttestCopyHeap cd root))
    (delegatedAttestRecord cd root).signature
def delegatedAttestInputMemory (cd : ByteArray) (root : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (Reasoning.Theory.writeWord (delegatedAttestSignatureMemory cd root) 288
    (UInt256.ofNat (delegatedAttestCopyHeap cd root))) 320 (calldataWord cd (root+UInt256.ofNat 160).toNat)

theorem delegatedAttestSchemaMemory_facts (cd : ByteArray) (root : UInt256) :
    (delegatedAttestSchemaMemory cd root).size = 256 ∧
    memLoad (UInt256.ofNat 64) (delegatedAttestSchemaMemory cd root) = UInt256.ofNat 352 ∧
    memLoad (UInt256.ofNat 224) (delegatedAttestSchemaMemory cd root) = calldataWord cd root.toNat ∧
    memLoad (UInt256.ofNat 96) (delegatedAttestSchemaMemory cd root) = ⟨0⟩ := by
  refine ⟨?_,?_,?_,?_⟩
  · simp only [delegatedAttestSchemaMemory,attestPublicInitialMemory,writeWord_sparse_size]; rfl
  · unfold delegatedAttestSchemaMemory
    rw [memLoad_write_below _ _ _ _ (by decide) (by rw [writeWord_sparse_size]; change 96 ≤ _; omega),memLoad_write_at _ _ _ (by decide)]
  · exact memLoad_write_at _ _ _ (by decide)
  · apply mloadWordValue_of_readWithPadding
    · change 96 < (Reasoning.Theory.writeWord _ 224 _).size
      rw [writeWord_sparse_size]; omega
    · change (Reasoning.Theory.writeWord _ 224 (calldataWord cd root.toNat)).readWithPadding 96 32 = _
      rw [writeWord_sparse_eq _ _ _ (by native_decide)]
      rw [readWithPadding_eq_extract _ _ (by
        simp only [ByteArray.size_append,ByteArray_zeroes_size,toByteArray_size]; native_decide)]
      rw [extract_append_left _ _ _ _ (by native_decide)]
      native_decide

theorem delegatedAttestInputMemory_view (cd : ByteArray) (root : UInt256)
    (hsize : cd.size < 2^255+4) (hd : delegatedAttestFieldsValid cd root)
    (hv : copyRequestValid 352 (delegatedAttestRecord cd root).data.data.size)
    (hh : delegatedAttestCopyHeap cd root+96 ≤ 2^64-1) :
    DelegatedAttestMemoryView (delegatedAttestInputMemory cd root) (UInt256.ofNat 224) (UInt256.ofNat 352)
      (UInt256.ofNat 544) (UInt256.ofNat (delegatedAttestCopyHeap cd root)) (delegatedAttestRecord cd root)
      (delegatedAttestCopyHeap cd root+96) ∧
    memLoad (UInt256.ofNat 64) (delegatedAttestInputMemory cd root) = UInt256.ofNat (delegatedAttestCopyHeap cd root+96) ∧
    memLoad (UInt256.ofNat 96) (delegatedAttestInputMemory cd root) = ⟨0⟩ := by
  let heap := delegatedAttestCopyHeap cd root
  have hb : heap+96 < UInt256.size := by change heap+96 < 2^256; change heap+96 ≤ 2^64-1 at hh; omega
  have hn : (UInt256.ofNat heap).toNat = heap := ulit_toNat' _ (by omega)
  have hm := requestCopyMemory_views (delegatedAttestSchemaMemory cd root) cd (delegatedAttestData cd root) (UInt256.ofNat 352)
    (by decide) (by decide) hsize hd.2.1 hv
  simp only [show allocateNext 352 192 = 544 by native_decide] at hm
  change MemoryPrefix (delegatedAttestSchemaMemory cd root) (delegatedAttestCopiedMemory cd root) 352 ∧
    AttestationRequestMemoryView (delegatedAttestCopiedMemory cd root) (UInt256.ofNat 352) (UInt256.ofNat 544) (delegatedAttestRecord cd root).data ∧
    memLoad (UInt256.ofNat 64) (delegatedAttestCopiedMemory cd root) = UInt256.ofNat heap ∧
    544 ≤ heap ∧ 544+32+32*(((delegatedAttestRecord cd root).data.data.size+31)/32) = heap ∧
    heap ≤ (delegatedAttestCopiedMemory cd root).size at hm
  have hlo : 576 ≤ heap := by omega
  have hd1 := hm.2.1.write_below 256 (UInt256.ofNat 352) (by decide) (by decide) (by decide)
  have hs := signatureCopyMemory_facts (delegatedAttestLinkedMemory cd root) (UInt256.ofNat heap)
    (delegatedAttestRecord cd root).signature (by rw [hn]; omega) (by rw [hn]; exact hb) hd.2.2.1.2
  simp only [hn] at hs
  change MemoryPrefix (delegatedAttestLinkedMemory cd root) (delegatedAttestSignatureMemory cd root) heap ∧
    SignatureMemoryView (delegatedAttestSignatureMemory cd root) (UInt256.ofNat heap) (delegatedAttestRecord cd root).signature ∧
    memLoad (UInt256.ofNat 64) (delegatedAttestSignatureMemory cd root) = UInt256.ofNat (heap+96) at hs
  have hd2 := hd1.preserve hs.1 hm.2.2.2.1 (le_of_eq hm.2.2.2.2.1) (by omega)
  have hd3 := hd2.write_below 288 (UInt256.ofNat heap) (by decide) (by decide) (by decide)
  have hd4 := hd3.write_below 320 (calldataWord cd (root+UInt256.ofNat 160).toNat) (by decide) (by decide) (by decide)
  have hs3 := hs.2.1.write_below 288 (UInt256.ofNat heap) (by rw [hn]; exact hb) (by rw [hn]; omega)
  have hs4 := hs3.write_below 320 (calldataWord cd (root+UInt256.ofNat 160).toNat) (by rw [hn]; exact hb) (by rw [hn]; omega)
  have hc : heap+96 ≤ (delegatedAttestSignatureMemory cd root).size := by
    simpa only [hn] using hs.2.1.covered
  have hschema : memLoad (UInt256.ofNat 224) (delegatedAttestCopiedMemory cd root) = calldataWord cd root.toNat :=
    (memLoad_of_prefix hm.1 _ (by decide) (by decide) (by rw [(delegatedAttestSchemaMemory_facts cd root).1]; decide)).trans
      (delegatedAttestSchemaMemory_facts cd root).2.2.1
  have hzero : memLoad (UInt256.ofNat 96) (delegatedAttestCopiedMemory cd root) = ⟨0⟩ :=
    (memLoad_of_prefix hm.1 _ (by decide) (by decide) (by rw [(delegatedAttestSchemaMemory_facts cd root).1]; decide)).trans
      (delegatedAttestSchemaMemory_facts cd root).2.2.2
  have hlinkedCover : heap ≤ (delegatedAttestLinkedMemory cd root).size := by
    unfold delegatedAttestLinkedMemory; rw [writeWord_sparse_size]; have := hm.2.2.2.2.2; omega
  have hsigLoad (off : Nat) (ho : off ∈ [96,224,256]) :
      memLoad (UInt256.ofNat off) (delegatedAttestSignatureMemory cd root) =
        if off = 96 then ⟨0⟩ else if off = 224 then calldataWord cd root.toNat else UInt256.ofNat 352 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    rcases ho with h|h|h <;> subst off
    · rw [memLoad_of_prefix hs.1 _ (by decide) (by change 128 ≤ heap; omega) (by change 128 ≤ _; omega)]
      unfold delegatedAttestLinkedMemory
      rw [memLoad_write_below _ _ _ _ (by decide) (by have := hm.2.2.2.2.2; change 128 ≤ _; omega),hzero]
      rfl
    · rw [memLoad_of_prefix hs.1 _ (by decide) (by change 256 ≤ heap; omega) (by change 256 ≤ _; omega)]
      unfold delegatedAttestLinkedMemory
      rw [memLoad_write_below _ _ _ _ (by decide) (by have := hm.2.2.2.2.2; change 256 ≤ _; omega),hschema]
      rfl
    · rw [memLoad_of_prefix hs.1 _ (by decide) (by change 288 ≤ heap; omega) (by change 288 ≤ _; omega)]
      exact memLoad_write_at _ _ _ (by decide)
  have hkeep (off : Nat) (ho : off ≤ 256) :
      memLoad (UInt256.ofNat off) (delegatedAttestInputMemory cd root) = memLoad (UInt256.ofNat off) (delegatedAttestSignatureMemory cd root) := by
    have hon : (UInt256.ofNat off).toNat = off := ulit_toNat' _ (by change off < 2^256; omega)
    unfold delegatedAttestInputMemory
    rw [memLoad_write_below _ _ _ _ (by rw [hon]; omega) (by rw [hon,writeWord_sparse_size]; omega),
      memLoad_write_below _ _ _ _ (by rw [hon]; omega) (by rw [hon]; omega)]
  refine ⟨⟨by decide,?_,by change 352 ≤ heap+96; omega,?_,?_,?_,?_,hd4,by change 544 ≤ heap+96; omega,?_,hs4,by rw [hn]⟩,?_,?_⟩
  · unfold delegatedAttestInputMemory; rw [writeWord_sparse_size]; change 352 ≤ _; omega
  · exact (hkeep 224 (by decide)).trans (hsigLoad 224 (by simp))
  · exact (hkeep 256 (by decide)).trans (hsigLoad 256 (by simp))
  · change memLoad (UInt256.ofNat 288) (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord _ 288 _) 320 _) = _
    rw [memLoad_write_below _ _ _ _ (by decide) (by rw [writeWord_sparse_size]; change 320 ≤ _; omega),memLoad_write_at _ _ _ (by decide)]
  · change UInt256.land (memLoad (UInt256.ofNat 320) (Reasoning.Theory.writeWord _ 320 _)) solcAddrMask = _
    rw [memLoad_write_at _ _ _ (by decide),solcAddrMask_clean hd.2.2.2]
    exact (addressWord_eq_ofNat_address hd.2.2.2).symm
  · change 544+32+32*(((delegatedAttestRecord cd root).data.data.size+31)/32) ≤ heap+96
    omega
  · exact (hkeep 64 (by decide)).trans hs.2.2
  · exact (hkeep 96 (by decide)).trans (hsigLoad 96 (by simp))

end Benchmarks.EAS.EAS
