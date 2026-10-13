import Benchmarks.EAS.EAS.DelegatedAttestMemory
import Benchmarks.EAS.EAS.VerifyBuffer
import Benchmarks.EAS.EAS.MappingHash
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def verifyAttestScratch (mem : ByteArray) (r : DelegatedAttestationRecord) : ByteArray :=
  twoWordHashMem (UInt256.ofNat r.attester.val) (UInt256.ofNat 0) mem
def verifyAttestBuffer (mem : ByteArray) (heap : Nat) (r : DelegatedAttestationRecord) (nonce : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (writeWordSequence (verifyAttestScratch mem r) (heap+32) (verifyAttestWords r nonce)) heap (UInt256.ofNat 256)

theorem verifyAttestScratch_prefix (mem : ByteArray) (r : DelegatedAttestationRecord) (limit : Nat) :
    MemoryPrefix mem (verifyAttestScratch mem r) limit :=
  (memoryPrefix_sparse_writeWord _ 0 _ _ (Or.inr (by decide))).trans
    (memoryPrefix_sparse_writeWord _ 32 _ _ (Or.inr (by decide)))

theorem verifyAttestScratch_slot (mem : ByteArray) (r : DelegatedAttestationRecord) :
    keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (verifyAttestScratch mem r) = nonceSlot r.attester := by
  unfold nonceSlot
  rw [keyValueToWord_address]
  exact mappingHash _ _ _

theorem verifyAttestFirstMemory {mem : ByteArray} {heap ptr dataPtr bytesPtr sigPtr : UInt256} {r : DelegatedAttestationRecord}
    (hv : DelegatedAttestMemoryView mem ptr dataPtr bytesPtr sigPtr r heap.toNat) :
    easBlocks.eas_block_13494_memory (mem := mem) (x0 := ptr) = verifyAttestScratch mem r := by
  have howner : UInt256.land (memLoad (ptr+UInt256.ofNat 96) mem)
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = UInt256.ofNat r.attester.val := hv.attester
  simp only [easBlocks.eas_block_13494_memory,howner]
  rfl

theorem verifyAttestFirstStack {ee : ExecutionEnv} {mem : ByteArray} {σ : AccountMap}
    {heap ptr dataPtr bytesPtr sigPtr : UInt256} {R : List UInt256} {r : DelegatedAttestationRecord}
    (hv : DelegatedAttestMemoryView mem ptr dataPtr bytesPtr sigPtr r heap.toNat) :
    easBlocks.eas_block_13494_stack (ee := ee) (mem := mem) (σ := σ) (x0 := ptr) (R := R) =
      (UInt256.ofNat 96::UInt256.ofNat 128::r.data.revocable.toUInt256::dataPtr::r.data.expirationTime::
      solcSlotWord σ ee (nonceSlot r.attester)::UInt256.ofNat r.data.recipient.val::r.schema::
      UInt256.ofNat 13723::sigPtr::UInt256.ofNat 13745::(ptr+UInt256.ofNat 96)::solcAddrMask::solcAddrMask::UInt256.ofNat 13753::R) := by
  have hm := hv.preserve (verifyAttestScratch_prefix mem r heap.toNat) heap.val.isLt
  have howner : UInt256.land (memLoad (ptr+UInt256.ofNat 96) mem)
      (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = UInt256.ofNat r.attester.val := hv.attester
  have hrecipient : UInt256.land (memLoad dataPtr (verifyAttestScratch mem r)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = UInt256.ofNat r.data.recipient.val :=
    (u256_land_comm _ _).trans hm.data.recipient
  have hexp : UInt256.land (memLoad (dataPtr+UInt256.ofNat 32) (verifyAttestScratch mem r)) (UInt256.ofNat 18446744073709551615) = r.data.expirationTime :=
    (u256_land_comm _ _).trans hm.data.expiration
  simp only [easBlocks.eas_block_13494_stack,howner,hv.dataPointer,hv.sigPointer]
  change (UInt256.ofNat 96::UInt256.ofNat 128::UInt256.isZero (UInt256.isZero (memLoad (dataPtr+UInt256.ofNat 64) (verifyAttestScratch mem r)))::dataPtr::
    UInt256.land (memLoad (dataPtr+UInt256.ofNat 32) (verifyAttestScratch mem r)) (UInt256.ofNat 18446744073709551615)::
    solcSlotWord σ ee (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 64) (verifyAttestScratch mem r))::
    UInt256.land (memLoad dataPtr (verifyAttestScratch mem r)) (UInt256.ofNat 1461501637330902918203684832716283019655932542975)::
    memLoad ptr (verifyAttestScratch mem r)::UInt256.ofNat 13723::sigPtr::UInt256.ofNat 13745::(ptr+UInt256.ofNat 96)::
    solcAddrMask::solcAddrMask::UInt256.ofNat 13753::R) = _
  rw [hm.data.revocable,hexp,hrecipient,hm.schema,verifyAttestScratch_slot]

theorem attestationRequest_keccak {mem : ByteArray} {ptr bytesPtr : UInt256} {r : AttestationRequestRecord} {limit : Nat}
    (hv : AttestationRequestMemoryView mem ptr bytesPtr r)
    (hend : bytesPtr.toNat+32+32*((r.data.size+31)/32) ≤ limit) (hb : limit < UInt256.size) :
    keccakWord (bytesPtr+UInt256.ofNat 32) (memLoad bytesPtr mem) mem = uInt256OfByteArray (KEC r.data) := by
  have hsize : r.data.size < UInt256.size := by omega
  rw [hv.length,keccakWord,uadd_word_ofNat_toNat bytesPtr 32 (by omega),ulit_toNat' _ hsize,hv.payload]
  exact (uInt256OfByteArray_eq _).symm

theorem verifyAttestLastMemory {mem : ByteArray} {heap ptr dataPtr bytesPtr sigPtr : UInt256} {r : DelegatedAttestationRecord}
    (hv : DelegatedAttestMemoryView mem ptr dataPtr bytesPtr sigPtr r heap.toNat)
    (hh : memLoad (UInt256.ofNat 64) mem = heap) (hb : heap.toNat+288 < UInt256.size) (nonce : UInt256) :
    easBlocks.eas_block_13605_memory (mem := verifyAttestScratch mem r)
      (x0 := UInt256.ofNat 96) (x1 := UInt256.ofNat 128) (x2 := r.data.revocable.toUInt256) (x3 := dataPtr)
      (x4 := r.data.expirationTime) (x5 := nonce) (x6 := UInt256.ofNat r.data.recipient.val) (x7 := r.schema) =
      verifyAttestBuffer mem heap.toNat r nonce := by
  have hm := hv.preserve (verifyAttestScratch_prefix mem r heap.toNat) heap.val.isLt
  have hfree : memLoad (UInt256.ofNat 64) (verifyAttestScratch mem r) = heap :=
    twoWordHashMem_heap _ _ _ _ (by have := hv.low; have := hv.covered; omega) hh
  have hhash := attestationRequest_keccak hm.data hm.bytesEnd heap.val.isLt
  have ho (n : Nat) (hn : n ≤ 288) : (heap+UInt256.ofNat n).toNat = heap.toNat+n := uadd_word_ofNat_toNat _ _ (by omega)
  simp only [easBlocks.eas_block_13605_memory,hfree,hm.data.pointer,hm.data.refUID,hhash,
    ho 32 (by decide),ho 64 (by decide),ho 96 (by decide),ho 128 (by decide),ho 160 (by decide),ho 192 (by decide),
    ho 224 (by decide),ho 256 (by decide),verifyAttestBuffer,verifyAttestWords,writeWordSequence,Reasoning.Theory.writeWord,
    Nat.add_assoc,Nat.reduceAdd]
  rfl

end Benchmarks.EAS.EAS
