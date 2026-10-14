import Benchmarks.EAS.EAS.DelegatedAttestRecordFinish
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def delegatedAttestBuildRecord (cd : ByteArray) (schema src sigSrc addrHead : UInt256) : DelegatedAttestationRecord :=
  ⟨schema,requestDataRecord cd src,signatureAt cd sigSrc,AccountAddress.ofNat (calldataWord cd addrHead.toNat).toNat⟩
def delegatedAttestBuildData (heap : UInt256) : UInt256 := UInt256.ofNat (heap.toNat+128)
def delegatedAttestBuildBytes (heap : UInt256) : UInt256 := UInt256.ofNat (heap.toNat+320)
def delegatedAttestBuildCopyHeap (cd : ByteArray) (src heap : UInt256) : Nat :=
  copyRequestNext (heap.toNat+128) (requestDataRecord cd src).data.size
def delegatedAttestBuildSchema (mem : ByteArray) (heap schema : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem 64 (delegatedAttestBuildData heap)) heap.toNat schema
def delegatedAttestBuildCopied (mem cd : ByteArray) (schema src heap : UInt256) : ByteArray :=
  requestCopyMemory (delegatedAttestBuildSchema mem heap schema) cd src (delegatedAttestBuildData heap)
def delegatedAttestBuildLinked (mem cd : ByteArray) (schema src heap : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (delegatedAttestBuildCopied mem cd schema src heap) (heap.toNat+32) (delegatedAttestBuildData heap)
def delegatedAttestBuildSignature (mem cd : ByteArray) (schema src sigSrc heap : UInt256) : ByteArray :=
  signatureCopyMemory (delegatedAttestBuildLinked mem cd schema src heap) (UInt256.ofNat (delegatedAttestBuildCopyHeap cd src heap))
    (signatureAt cd sigSrc)
def delegatedAttestBuildMemory (mem cd : ByteArray) (schema src sigSrc addrHead heap : UInt256) : ByteArray :=
  delegatedAttestRecordFinish (delegatedAttestBuildSignature mem cd schema src sigSrc heap) heap
    (UInt256.ofNat (delegatedAttestBuildCopyHeap cd src heap)) (delegatedAttestBuildRecord cd schema src sigSrc addrHead).attester

def delegatedAttestBuildValid (cd : ByteArray) (src sigSrc addrHead heap : UInt256) : Prop :=
  (calldataWord cd addrHead.toNat).toNat < EVM.addressModulus ∧ heap.toNat+128 ≤ 2^64-1 ∧
    requestDataValid cd src ∧ copyRequestValid (heap.toNat+128) (requestDataRecord cd src).data.size ∧
    signatureAtValid cd sigSrc ∧ delegatedAttestBuildCopyHeap cd src heap+96 ≤ 2^64-1
instance (cd : ByteArray) (src sigSrc addrHead heap : UInt256) : Decidable (delegatedAttestBuildValid cd src sigSrc addrHead heap) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

theorem delegatedAttestBuildSchema_facts (mem : ByteArray) (heap schema : UInt256)
    (hlo : 96≤heap.toNat) (hh : heap.toNat+128 < UInt256.size) (hm : 96≤mem.size) :
    MemoryPrefix mem (delegatedAttestBuildSchema mem heap schema) heap.toNat ∧
    memLoad (UInt256.ofNat 64) (delegatedAttestBuildSchema mem heap schema)=delegatedAttestBuildData heap ∧
    memLoad heap (delegatedAttestBuildSchema mem heap schema)=schema ∧
    heap.toNat+32 ≤ (delegatedAttestBuildSchema mem heap schema).size := by
  refine ⟨(memoryPrefix_sparse_writeWord mem 64 heap.toNat _ (Or.inr (by decide))).trans
    (memoryPrefix_sparse_writeWord _ heap.toNat heap.toNat _ (Or.inl (le_refl _))),?_,?_,?_⟩
  · unfold delegatedAttestBuildSchema
    rw [memLoad_write_below _ _ _ _ hlo (by rw [writeWord_sparse_size];change 96≤_;omega),memLoad_write_at _ _ _ (by decide)]
  · have hw := memLoad_write_at (Reasoning.Theory.writeWord mem 64 (delegatedAttestBuildData heap)) heap.toNat schema heap.val.isLt
    simpa only [u256_ofNat_toNat] using hw
  · unfold delegatedAttestBuildSchema
    rw [writeWord_sparse_size]
    omega

theorem delegatedAttestBuildMemory_facts {mem cd : ByteArray} {schema src sigSrc addrHead heap : UInt256}
    (hlo : 96≤heap.toNat) (hm : 96≤mem.size) (hsize : cd.size<2^255+4)
    (hv : delegatedAttestBuildValid cd src sigSrc addrHead heap) :
    MemoryPrefix mem (delegatedAttestBuildMemory mem cd schema src sigSrc addrHead heap) heap.toNat ∧
    DelegatedAttestMemoryView (delegatedAttestBuildMemory mem cd schema src sigSrc addrHead heap) heap
      (delegatedAttestBuildData heap) (delegatedAttestBuildBytes heap) (UInt256.ofNat (delegatedAttestBuildCopyHeap cd src heap))
      (delegatedAttestBuildRecord cd schema src sigSrc addrHead) (delegatedAttestBuildCopyHeap cd src heap+96) ∧
    memLoad (UInt256.ofNat 64) (delegatedAttestBuildMemory mem cd schema src sigSrc addrHead heap)=
      UInt256.ofNat (delegatedAttestBuildCopyHeap cd src heap+96) := by
  let dp := delegatedAttestBuildData heap
  let bp := delegatedAttestBuildBytes heap
  let next := delegatedAttestBuildCopyHeap cd src heap
  let m1 := delegatedAttestBuildSchema mem heap schema
  let m2 := delegatedAttestBuildCopied mem cd schema src heap
  let m3 := delegatedAttestBuildLinked mem cd schema src heap
  let m4 := delegatedAttestBuildSignature mem cd schema src sigSrc heap
  have hb : heap.toNat+320<UInt256.size := by have := hv.2.1;change _<2^256;omega
  have hdp : dp.toNat=heap.toNat+128 := ulit_toNat' _ (by omega)
  have hbp : bp.toNat=heap.toNat+320 := ulit_toNat' _ hb
  have hn : (UInt256.ofNat next).toNat=next := ulit_toNat' _ (by have hv96 : next+96≤2^64-1 := hv.2.2.2.2.2;change _<2^256;omega)
  have hn96 : (UInt256.ofNat (next+96)).toNat=next+96 := ulit_toNat' _ (by have hv96 : next+96≤2^64-1 := hv.2.2.2.2.2;change _<2^256;omega)
  have hs := delegatedAttestBuildSchema_facts mem heap schema hlo (by omega) hm
  have hc := requestCopyMemory_views m1 cd src dp (by rw [hdp];omega) (by rw [hdp];exact hv.2.1) hsize hv.2.2.1 (by rw [hdp];exact hv.2.2.2.1)
  have ha : UInt256.ofNat (allocateNext dp.toNat 192)=bp := by
    have han : allocateNext dp.toNat 192=dp.toNat+192 := fixedAllocation_next .bytes192 (by rw [hdp];exact hv.2.1)
    rw [han,hdp]
    rfl
  dsimp only at hc
  rw [ha] at hc
  simp only [hdp] at hc
  change MemoryPrefix m1 m2 (heap.toNat+128) ∧ AttestationRequestMemoryView m2 dp bp (requestDataRecord cd src) ∧
    memLoad (UInt256.ofNat 64) m2=UInt256.ofNat next ∧ heap.toNat+128+192≤next ∧
    bp.toNat+32+32*(((requestDataRecord cd src).data.size+31)/32)=next ∧ next≤m2.size at hc
  have hp3 : MemoryPrefix m2 m3 heap.toNat := memoryPrefix_sparse_writeWord m2 (heap.toNat+32) heap.toNat dp (Or.inl (by omega))
  have hd3 := hc.2.1.write_below (heap.toNat+32) dp (by rw [hdp];omega) (by rw [hdp];omega) (by rw [hbp];omega)
  have hcover3 : heap.toNat+128+192≤m3.size := by simpa only [hdp] using hd3.covered
  have hsc2 : memLoad heap m2=schema := (memLoad_of_prefix hc.1 heap hlo (by omega) hs.2.2.2).trans hs.2.2.1
  have hsc3 : memLoad heap m3=schema := by
    dsimp only [m3,delegatedAttestBuildLinked]
    rw [memLoad_write_below _ _ _ _ (le_refl _) (by change heap.toNat+32≤m2.size;omega)]
    exact hsc2
  have hfree3 : memLoad (UInt256.ofNat 64) m3=UInt256.ofNat next := by
    dsimp only [m3,delegatedAttestBuildLinked]
    rw [memLoad_write_below _ _ _ _ (by change 96≤_;omega) (by change 96≤m2.size;omega)]
    exact hc.2.2.1
  have hptr3 : memLoad (heap+UInt256.ofNat 32) m3=dp := by
    have hw : heap+UInt256.ofNat 32=UInt256.ofNat (heap.toNat+32) := by
      apply u256_inj
      rw [uadd_word_ofNat_toNat _ _ (by omega),ulit_toNat' _ (by omega)]
    rw [hw]
    exact memLoad_write_at _ _ _ (by omega)
  have hsig := signatureCopyMemory_facts m3 (UInt256.ofNat next) (signatureAt cd sigSrc)
    (by rw [hn];omega) (by rw [hn];have hv96 : next+96≤2^64-1 := hv.2.2.2.2.2;change _<2^256;omega) hv.2.2.2.2.1.2
  simp only [hn] at hsig
  have hd4 := hd3.preserve hsig.1 (by rw [hdp];omega) (le_of_eq hc.2.2.2.2.1) (by change _<2^256;have hv96 : next+96≤2^64-1 := hv.2.2.2.2.2;omega)
  have hs4 : memLoad heap m4=schema :=
    (memLoad_of_prefix hsig.1 heap hlo (by omega) (by omega)).trans hsc3
  have hp4 : memLoad (heap+UInt256.ofNat 32) m4=dp :=
    (memLoad_of_prefix hsig.1 _ (by rw [uadd_word_ofNat_toNat _ _ (by omega)];omega)
      (by rw [uadd_word_ofNat_toNat _ _ (by omega)];omega)
      (by rw [uadd_word_ofNat_toNat _ _ (by omega)];omega)).trans hptr3
  have hf := delegatedAttestRecordFinish_facts (mem := m4) (ptr := heap) (data := dp) (bytes := bp)
    (sig := UInt256.ofNat next) (heap := UInt256.ofNat (next+96)) (r := delegatedAttestBuildRecord cd schema src sigSrc addrHead)
    hlo (UInt256.ofNat (next+96)).val.isLt (by rw [hbp];omega) (by rw [hdp]) (by rw [hn];omega)
    (by rw [hdp,hn96];omega) (by rw [hn96];change bp.toNat+32+32*(((requestDataRecord cd src).data.size+31)/32)≤next+96;omega)
    (by rw [hn,hn96]) hd4 hsig.2.1 hs4 hp4 (by simpa only [hn] using hsig.2.2)
  simp only [hn96] at hf
  exact ⟨(((hs.1.trans (hc.1.mono (by omega))).trans hp3).trans (hsig.1.mono (by omega))).trans hf.1,hf.2.1,hf.2.2⟩

end Benchmarks.EAS.EAS
