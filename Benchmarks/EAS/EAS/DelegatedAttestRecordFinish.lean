import Benchmarks.EAS.EAS.DelegatedAttestPrepareMemory
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def delegatedAttestRecordFinish (mem : ByteArray) (ptr sig : UInt256) (attester : AccountAddress) : ByteArray :=
  Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem (ptr.toNat+64) sig)
    (ptr.toNat+96) (UInt256.ofNat attester.val)

theorem delegatedAttestRecordFinish_facts {mem : ByteArray} {ptr data bytes sig heap : UInt256}
    {r : DelegatedAttestationRecord}
    (hlo : 96 ≤ ptr.toNat) (hh : heap.toNat < UInt256.size)
    (hbr : ptr.toNat+128 ≤ bytes.toNat)
    (hr : ptr.toNat+128 ≤ data.toNat) (hsr : ptr.toNat+128 ≤ sig.toNat)
    (hde : data.toNat+192 ≤ heap.toNat) (hbe : bytes.toNat+32+32*((r.data.data.size+31)/32) ≤ heap.toNat)
    (hse : sig.toNat+96 ≤ heap.toNat)
    (hd : AttestationRequestMemoryView mem data bytes r.data) (hs : SignatureMemoryView mem sig r.signature)
    (hsc : memLoad ptr mem=r.schema) (hdp : memLoad (ptr+UInt256.ofNat 32) mem=data)
    (hfree : memLoad (UInt256.ofNat 64) mem=heap) :
    MemoryPrefix mem (delegatedAttestRecordFinish mem ptr sig r.attester) ptr.toNat ∧
    DelegatedAttestMemoryView (delegatedAttestRecordFinish mem ptr sig r.attester) ptr data bytes sig r heap.toNat ∧
    memLoad (UInt256.ofNat 64) (delegatedAttestRecordFinish mem ptr sig r.attester)=heap := by
  have hb : ptr.toNat+128 < UInt256.size := by omega
  have hc := hs.covered
  have hds := hd.covered
  have hd1 := hd.write_below (ptr.toNat+64) sig (by omega) (by omega) (by omega)
  have hd2 := hd1.write_below (ptr.toNat+96) (UInt256.ofNat r.attester.val) (by omega) (by omega) (by omega)
  have hs1 := hs.write_below (ptr.toNat+64) sig (by omega) (by omega)
  have hs2 := hs1.write_below (ptr.toNat+96) (UInt256.ofNat r.attester.val) (by omega) (by omega)
  have hoff (n : Nat) (hn : n≤96) : (ptr+UInt256.ofNat n).toNat=ptr.toNat+n := uadd_word_ofNat_toNat _ _ (by omega)
  have keep (p : UInt256) (hp : p.toNat+32 ≤ ptr.toNat+64) :
      memLoad p (delegatedAttestRecordFinish mem ptr sig r.attester)=memLoad p mem := by
    unfold delegatedAttestRecordFinish
    rw [memLoad_write_below _ _ _ _ (by omega) (by rw [writeWord_sparse_size];omega),
      memLoad_write_below _ _ _ _ hp (by omega)]
  refine ⟨(memoryPrefix_sparse_writeWord mem (ptr.toNat+64) ptr.toNat sig (Or.inl (by omega))).trans
    (memoryPrefix_sparse_writeWord _ (ptr.toNat+96) ptr.toNat _ (Or.inl (by omega))),
    ⟨hlo,?_,by omega,(keep ptr (by omega)).trans hsc,(keep _ (by rw [hoff 32 (by decide)])).trans hdp,
      ?_,?_,hd2,hde,hbe,hs2,hse⟩,(keep _ (by change 96≤ptr.toNat+64;omega)).trans hfree⟩
  · unfold delegatedAttestRecordFinish
    rw [writeWord_sparse_size]
    omega
  · unfold delegatedAttestRecordFinish
    rw [memLoad_write_below _ _ _ _ (by rw [hoff 64 (by decide)])
      (by rw [hoff 64 (by decide),writeWord_sparse_size];omega)]
    have hptr : ptr+UInt256.ofNat 64=UInt256.ofNat (ptr.toNat+64) := by
      apply u256_inj
      rw [hoff 64 (by decide),ulit_toNat' _ (by omega)]
    rw [hptr,memLoad_write_at _ _ _ (by omega)]
  · unfold delegatedAttestRecordFinish
    have hptr : ptr+UInt256.ofNat 96=UInt256.ofNat (ptr.toNat+96) := by
      apply u256_inj
      rw [hoff 96 (by decide),ulit_toNat' _ (by omega)]
    rw [hptr,memLoad_write_at _ _ _ (by omega)]
    exact addressWord_val_clean r.attester

end Benchmarks.EAS.EAS
