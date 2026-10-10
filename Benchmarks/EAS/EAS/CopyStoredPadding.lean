import Benchmarks.EAS.EAS.StoredRecord
import Benchmarks.EAS.EAS.RecordPadding
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- GENERALIZES memoryPrefix_reserve_write: two writes at the same boundary preserve the prefix regardless of their values.
theorem memoryPrefix_boundary_values (mem : ByteArray) (off : Nat) (a b : UInt256) :
    MemoryPrefix (Reasoning.Theory.writeWord mem off a) (Reasoning.Theory.writeWord mem off b) off := by
  refine ⟨by simp only [writeWord_sparse_size]; exact le_refl _,fun read hlo hhi hin => ?_⟩
  by_cases hm : off ≤ mem.size
  · rw [writeWord_sparse_read_preserved mem off read a (Or.inl ⟨hhi,by omega⟩),
      writeWord_sparse_read_preserved mem off read b (Or.inl ⟨hhi,by omega⟩)]
  · have hs : (mem++ByteArray.zeroes (off-mem.size)).size = off := by
      rw [ByteArray.size_append,ByteArray_zeroes_size]; omega
    rw [writeWord_sparse_eq mem off a (by omega),writeWord_sparse_eq mem off b (by omega)]
    rw [readWithPadding_eq_extract _ read (by rw [ByteArray.size_append,hs,toByteArray_size]; omega),
      readWithPadding_eq_extract _ read (by rw [ByteArray.size_append,hs,toByteArray_size]; omega)]
    rw [extract_append_left (mem++ByteArray.zeroes (off-mem.size)) b.toByteArray _ _ (by rw [hs]; exact hhi),
      extract_append_left (mem++ByteArray.zeroes (off-mem.size)) a.toByteArray _ _ (by rw [hs]; exact hhi)]

theorem copyStoredOutputMemory_padding (evm : EVM.State) (word heap : UInt256) (mem : ByteArray)
    (hv : copyStoredValid evm word heap.toNat) :
    MemoryPrefix (recordPadding mem heap.toNat) (copyStoredOutputMemory evm word heap mem) heap.toNat := by
  apply MemoryPrefix.trans (b := copyStoredFieldsMemory mem heap evm.accountMap evm.executionEnv (dbSlot word))
  · let m := Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat 320))
    let w := solcSlotWord evm.accountMap evm.executionEnv (dbSlot word)
    have hp := memoryPrefix_boundary_values m heap.toNat ⟨0⟩ w
    have ht := writeWordSequence_prefix (Reasoning.Theory.writeWord m heap.toNat w)
      (heap.toNat+32) heap.toNat (storedAttestationWords evm.accountMap evm.executionEnv (dbSlot word)).tail (by omega)
    simpa only [recordPadding,copyStoredFieldsMemory,storedAttestationWords,List.tail_cons,writeWordSequence,m,w] using hp.trans ht
  · exact (copyStoredOutputMemory_prefix evm word heap mem hv.1).mono (by omega)

end Benchmarks.EAS.EAS
