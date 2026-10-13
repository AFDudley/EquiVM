import Benchmarks.EAS.EAS.DelegatedRevokeMemory
import Benchmarks.EAS.EAS.RecordUID
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def delegatedRevokeRecordMemory (mem : ByteArray) (heap data sig : UInt256) (r : DelegatedRevocationRecord) : ByteArray :=
  writeWordSequence (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (heap.toNat+128))) heap.toNat
    [r.schema,data,sig,UInt256.ofNat r.revoker.val]

theorem delegatedRevokeRecordMemory_facts {mem : ByteArray} {heap data sig : UInt256} {r : DelegatedRevocationRecord}
    (hlo : 96 ≤ heap.toNat) (hh : heap.toNat+128 < UInt256.size)
    (hd : RevocationRequestMemoryView mem data r.data) (hde : data.toNat+64 ≤ heap.toNat)
    (hs : SignatureMemoryView mem sig r.signature) (hse : sig.toNat+96 ≤ heap.toNat) :
    MemoryPrefix mem (delegatedRevokeRecordMemory mem heap data sig r) heap.toNat ∧
    DelegatedRevokeMemoryView (delegatedRevokeRecordMemory mem heap data sig r) heap data sig r (heap.toNat+128) ∧
    memLoad (UInt256.ofNat 64) (delegatedRevokeRecordMemory mem heap data sig r) = UInt256.ofNat (heap.toNat+128) := by
  let words := [r.schema,data,sig,UInt256.ofNat r.revoker.val]
  let final := delegatedRevokeRecordMemory mem heap data sig r
  have hp : MemoryPrefix mem final heap.toNat :=
    (memoryPrefix_sparse_writeWord mem 64 heap.toNat _ (Or.inr (by decide))).trans
      (writeWordSequence_prefix _ heap.toNat heap.toNat words (le_refl _))
  have hc : heap.toNat+128 ≤ final.size :=
    writeWordSequence_covers _ heap.toNat words (by change [_ ,_,_,_] ≠ []; intro h; cases h)
  have hget (i : Nat) (hi : i<4) : memLoad (UInt256.ofNat (heap.toNat+32*i)) final = words[i] :=
    writeWordSequence_load_index _ _ _ _ hi (by omega)
  have hw (n : Nat) (hn : n≤96) : heap+UInt256.ofNat n = UInt256.ofNat (heap.toNat+n) := by
    apply u256_inj
    rw [uadd_word_ofNat_toNat _ _ (by omega),ulit_toNat' _ (by omega)]
  refine ⟨hp,⟨hlo,hc,le_refl _,?_,?_,?_,?_,hd.preserve hp hde heap.val.isLt,
    by omega,hs.preserve hp hse heap.val.isLt,by omega⟩,?_⟩
  · simpa only [Nat.mul_zero,Nat.add_zero,u256_ofNat_toNat,List.getElem_cons_zero,words] using hget 0 (by decide)
  · rw [hw 32 (by decide)]; exact hget 1 (by decide)
  · rw [hw 64 (by decide)]; exact hget 2 (by decide)
  · rw [hw 96 (by decide),hget 3 (by decide)]
    exact addressWord_val_clean r.revoker
  · exact writeWordSequence_setFree_load64 _ _ _ _ hlo

end Benchmarks.EAS.EAS
