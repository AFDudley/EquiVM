import Benchmarks.EAS.EAS.DelegatedRevokeMemory
import Benchmarks.EAS.EAS.VerifyBuffer
import Benchmarks.EAS.EAS.MappingHash
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def verifyRevokeScratch (mem : ByteArray) (r : DelegatedRevocationRecord) : ByteArray :=
  twoWordHashMem (UInt256.ofNat r.revoker.val) (UInt256.ofNat 0) mem
def verifyRevokeBuffer (mem : ByteArray) (heap : Nat) (r : DelegatedRevocationRecord) (nonce : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (writeWordSequence (verifyRevokeScratch mem r) (heap+32) (verifyRevokeWords r nonce)) heap (UInt256.ofNat 128)

theorem verifyRevokeScratch_prefix (mem : ByteArray) (r : DelegatedRevocationRecord) (limit : Nat) :
    MemoryPrefix mem (verifyRevokeScratch mem r) limit :=
  (memoryPrefix_sparse_writeWord _ 0 _ _ (Or.inr (by decide))).trans
    (memoryPrefix_sparse_writeWord _ 32 _ _ (Or.inr (by decide)))

theorem verifyRevokeScratch_slot (mem : ByteArray) (r : DelegatedRevocationRecord) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (verifyRevokeScratch mem r) = nonceSlot r.revoker := by
  unfold nonceSlot
  rw [keyValueToWord_address]
  exact mappingHash _ _ _

theorem verifyRevokeFirstStack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap}
    {heap ptr dataPtr sigPtr : UInt256} {R : List UInt256} {r : DelegatedRevocationRecord}
    (hv : DelegatedRevokeMemoryView mem ptr dataPtr sigPtr r heap.toNat)
    (hh : memLoad (UInt256.ofNat 64) mem = heap) :
    easBlocks.eas_block_13806_stack (ee := ee) (mem := mem) (σ := σ) (x0 := ptr) (R := R) =
      (UInt256.ofNat 128::solcSlotWord σ ee (nonceSlot r.revoker)::heap::(heap+UInt256.ofNat 32)::
      UInt256.ofNat 13723::sigPtr::UInt256.ofNat 13745::(ptr+UInt256.ofNat 96)::solcAddrMask::solcAddrMask::UInt256.ofNat 13753::R) := by
  have hfree : memLoad (UInt256.ofNat 64) (verifyRevokeScratch mem r) = heap :=
    twoWordHashMem_heap _ _ _ _ (by have := hv.low; have := hv.covered; omega) hh
  have hrev : UInt256.land (memLoad (ptr+UInt256.ofNat 96) mem)
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = UInt256.ofNat r.revoker.val := hv.revoker
  simp only [easBlocks.eas_block_13806_stack,hrev,hv.sigPointer]
  change (UInt256.ofNat 128::solcSlotWord σ ee (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (verifyRevokeScratch mem r))::
    memLoad (UInt256.ofNat 64) (verifyRevokeScratch mem r)::(memLoad (UInt256.ofNat 64) (verifyRevokeScratch mem r)+UInt256.ofNat 32)::
    UInt256.ofNat 13723::sigPtr::UInt256.ofNat 13745::(ptr+UInt256.ofNat 96)::solcAddrMask::solcAddrMask::UInt256.ofNat 13753::R) = _
  rw [hfree,verifyRevokeScratch_slot]

theorem verifyRevokeFirstMemory {mem : ByteArray} {heap ptr dataPtr sigPtr : UInt256} {r : DelegatedRevocationRecord}
    (hv : DelegatedRevokeMemoryView mem ptr dataPtr sigPtr r heap.toNat)
    (hh : memLoad (UInt256.ofNat 64) mem = heap) (hb : heap.toNat+160 < UInt256.size) :
    easBlocks.eas_block_13806_memory (mem := mem) (x0 := ptr) =
      writeWordSequence (verifyRevokeScratch mem r) (heap.toNat+32) [revokeTypeHash,r.schema,r.data.uid] := by
  have hm := verifyRevokeScratch_prefix mem r heap.toNat
  have hspan := hv.span
  have hlo := hv.low
  have hc := hv.covered
  have hdlo := hv.data.low
  have hdc := hv.data.covered
  have hde := hv.dataEnd
  have ho (n : Nat) (hn : n ≤ 160) : (heap+UInt256.ofNat n).toNat = heap.toNat+n := uadd_word_ofNat_toNat _ _ (by omega)
  have hfree : memLoad (UInt256.ofNat 64) (verifyRevokeScratch mem r) = heap := twoWordHashMem_heap _ _ _ _ (by omega) hh
  have hschema : memLoad ptr (verifyRevokeScratch mem r) = r.schema :=
    (memLoad_of_prefix hm _ hlo (by omega) (by omega)).trans hv.schema
  have huid : memLoad dataPtr (verifyRevokeScratch mem r) = r.data.uid :=
    (memLoad_of_prefix hm _ hdlo (by omega) (by omega)).trans hv.data.uid
  have hrev : UInt256.land (memLoad (ptr+UInt256.ofNat 96) mem)
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = UInt256.ofNat r.revoker.val := hv.revoker
  simp only [easBlocks.eas_block_13806_memory,hrev,hv.dataPointer]
  change (memLoad dataPtr (verifyRevokeScratch mem r)).toByteArray.write 0
    ((memLoad ptr (verifyRevokeScratch mem r)).toByteArray.write 0
      (revokeTypeHash.toByteArray.write 0 (verifyRevokeScratch mem r)
        (memLoad (UInt256.ofNat 64) (verifyRevokeScratch mem r)+UInt256.ofNat 32).toNat 32)
      (memLoad (UInt256.ofNat 64) (verifyRevokeScratch mem r)+UInt256.ofNat 64).toNat 32)
    (memLoad (UInt256.ofNat 64) (verifyRevokeScratch mem r)+UInt256.ofNat 96).toNat 32 = _
  rw [hfree,hschema,huid,ho 32 (by decide),ho 64 (by decide),ho 96 (by decide)]
  simp only [writeWordSequence,Reasoning.Theory.writeWord,Nat.add_assoc,Nat.reduceAdd]

theorem verifyRevokeLastMemory (mem : ByteArray) (heap : UInt256) (r : DelegatedRevocationRecord) (nonce : UInt256)
    (hb : heap.toNat+160 < UInt256.size) :
    easBlocks.eas_block_13942_memory (mem := writeWordSequence (verifyRevokeScratch mem r) (heap.toNat+32) [revokeTypeHash,r.schema,r.data.uid])
      (x0 := UInt256.ofNat 128) (x1 := nonce) (x2 := heap) = verifyRevokeBuffer mem heap.toNat r nonce := by
  simp only [easBlocks.eas_block_13942_memory,verifyRevokeBuffer,verifyRevokeWords,writeWordSequence,
    Reasoning.Theory.writeWord,uadd_word_ofNat_toNat heap 128 (by omega),Nat.add_assoc,Nat.reduceAdd]

end Benchmarks.EAS.EAS
