import Benchmarks.EAS.EAS.TypedDataSource
import Benchmarks.EAS.EAS.WordSequence
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def typedDataPrefixWord : UInt256 := ⟨11309588061646438093662687302255421419811724423900836950936401294474059186176⟩
def typedDataBuffer (mem : ByteArray) (heap : Nat) (domain structHash : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord
    (writeWordSequence (Reasoning.Theory.writeWord mem (heap+32) typedDataPrefixWord) (heap+34) [domain,structHash])
    heap (UInt256.ofNat 66)
def typedDataMemory (mem : ByteArray) (heap : Nat) (domain structHash : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord (typedDataBuffer mem heap domain structHash) 64 (UInt256.ofNat (allocateNext heap 128))

theorem typedDataBuffer_covers (mem : ByteArray) (heap : Nat) (domain structHash : UInt256) :
    heap+98 ≤ (typedDataBuffer mem heap domain structHash).size := by
  have h := writeWordSequence_covers (Reasoning.Theory.writeWord mem (heap+32) typedDataPrefixWord)
    (heap+34) [domain,structHash] (by simp only [ne_eq,List.cons_ne_nil,not_false_eq_true])
  simp only [List.length_cons,List.length_nil] at h
  rw [typedDataBuffer,writeWord_sparse_size]
  omega

theorem typedDataBuffer_payload (mem : ByteArray) (heap : Nat) (domain structHash : UInt256) :
    (typedDataBuffer mem heap domain structHash).readWithPadding (heap+32) 66 = typedDataPayload domain structHash := by
  let base := Reasoning.Theory.writeWord mem (heap+32) typedDataPrefixWord
  let seq := writeWordSequence base (heap+34) [domain,structHash]
  have hb : heap+64 ≤ base.size := by simp only [base,writeWord_sparse_size]; omega
  have hc : heap+98 ≤ seq.size := by
    have h := writeWordSequence_covers base (heap+34) [domain,structHash] (by simp only [ne_eq,List.cons_ne_nil,not_false_eq_true])
    exact h
  have hhead : seq.readWithPadding (heap+32) 2 = ⟨#[25,1]⟩ := by
    unfold seq
    simp only [writeWordSequence,Nat.add_assoc,Nat.reduceAdd]
    rw [writeWord_read_preserved_len _ (heap+66) (heap+32) 2 _
      (by rw [writeWord_sparse_size]; have hu := lt_usize 0 (by decide); omega)
      (Or.inl ⟨by omega,by rw [writeWord_sparse_size]; omega⟩) (by decide) (by decide)]
    rw [writeWord_read_preserved_len base (heap+34) (heap+32) 2 domain
      (by have hu := lt_usize 0 (by decide); omega) (Or.inl ⟨by omega,by omega⟩) (by decide) (by decide)]
    have h := writeWord_sparse_read_window mem (heap+32) 0 2 typedDataPrefixWord (by decide) (by decide) (by decide)
    simpa only [Nat.add_zero,show typedDataPrefixWord.toByteArray.extract 0 (0+2) = ⟨#[25,1]⟩ from by decide +kernel] using h
  change (Reasoning.Theory.writeWord seq heap (UInt256.ofNat 66)).readWithPadding (heap+32) 66 = _
  rw [writeWord_read_preserved_len seq heap (heap+32) 66 _
    (by have hu := lt_usize 0 (by decide); omega) (Or.inr ⟨by omega,by omega⟩) (by decide) (by decide)]
  rw [show 66 = 2+64 from rfl,byteArray_readWithPadding_split_unbounded seq (heap+32) 2 64
    (by decide) (by decide) (by omega),hhead]
  have htail : seq.readWithPadding (heap+34) 64 = wordBytes [domain,structHash] := writeWordSequence_read base (heap+34) [domain,structHash]
  rw [show heap+32+2 = heap+34 by omega,htail,wordBytes_eq_list]
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [typedDataPayload,List.flatMap_cons,List.flatMap_nil,List.append_nil,ByteArray.data_append,
    List.data_toByteArray,Array.toList_append,List.toList_toArray,List.append_assoc]

theorem typedDataMemory_payload (mem : ByteArray) (heap : Nat) (domain structHash : UInt256) (hlo : 96 ≤ heap) :
    (typedDataMemory mem heap domain structHash).readWithPadding (heap+32) 66 = typedDataPayload domain structHash := by
  have hc := typedDataBuffer_covers mem heap domain structHash
  rw [typedDataMemory,writeWord_read_preserved_len _ 64 (heap+32) 66 _
    (by have hu := lt_usize 0 (by decide); omega) (Or.inr ⟨by omega,by omega⟩) (by decide) (by decide)]
  exact typedDataBuffer_payload mem heap domain structHash

theorem typedDataMemory_header (mem : ByteArray) (heap : Nat) (domain structHash : UInt256) (hlo : 96 ≤ heap) :
    (typedDataMemory mem heap domain structHash).readWithPadding heap 32 = (UInt256.ofNat 66).toByteArray := by
  rw [typedDataMemory,writeWord_sparse_read_preserved _ 64 heap _ (Or.inr ⟨hlo,by rw [typedDataBuffer,writeWord_sparse_size]; omega⟩)]
  exact writeWord_sparse_read_back _ _ _

theorem typedDataMemory_free (mem : ByteArray) (heap : Nat) (domain structHash : UInt256) :
    memLoad (UInt256.ofNat 64) (typedDataMemory mem heap domain structHash) = UInt256.ofNat (allocateNext heap 128) := by
  apply mloadWordValue_of_readWithPadding
  · rw [typedDataMemory,writeWord_sparse_size]; change 64 < _; omega
  exact writeWord_sparse_read_back _ _ _

theorem typedDataMemory_prefix (mem : ByteArray) (heap : Nat) (domain structHash : UInt256) :
    MemoryPrefix mem (typedDataMemory mem heap domain structHash) heap := by
  exact ((memoryPrefix_sparse_writeWord mem (heap+32) heap _ (Or.inl (by omega))).trans
    (writeWordSequence_prefix _ (heap+34) heap [domain,structHash] (by omega))).trans
    ((memoryPrefix_sparse_writeWord _ heap heap _ (Or.inl (le_refl _))).trans
      (memoryPrefix_sparse_writeWord _ 64 heap _ (Or.inr (by decide))))

theorem typedDataMemory_keccak (mem : ByteArray) (heap : UInt256) (domain structHash : UInt256)
    (hlo : 96 ≤ heap.toNat) (hb : heap.toNat+98 < UInt256.size) :
    keccakWord (heap+UInt256.ofNat 32) (memLoad heap (typedDataMemory mem heap.toNat domain structHash))
      (typedDataMemory mem heap.toNat domain structHash) = typedDataWord domain structHash := by
  have hc := typedDataBuffer_covers mem heap.toNat domain structHash
  have hh : memLoad heap (typedDataMemory mem heap.toNat domain structHash) = UInt256.ofNat 66 :=
    mloadWordValue_of_readWithPadding (by rw [typedDataMemory,writeWord_sparse_size]; omega)
      (typedDataMemory_header mem heap.toNat domain structHash hlo)
  rw [hh,keccakWord,uadd_word_ofNat_toNat heap 32 (by omega)]
  change UInt256.ofNat (fromByteArrayBigEndian (KEC
    ((typedDataMemory mem heap.toNat domain structHash).readWithPadding (heap.toNat+32) 66))) = _
  rw [typedDataMemory_payload mem heap.toNat domain structHash hlo]
  exact (uInt256OfByteArray_eq _).symm

end Benchmarks.EAS.EAS
