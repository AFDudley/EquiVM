import Benchmarks.EAS.EAS.RecordArrayStep
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- GENERALIZES Reasoning.Memory.write32_read_above_len to arbitrary in-bounds window lengths.
theorem writeWord_read_above_len (mem : ByteArray) (off read len : Nat) (word : UInt256)
    (hlo : off+32 ≤ read) (hin : read+len ≤ mem.size) :
    (Reasoning.Theory.writeWord mem off word).readWithPadding read len = mem.readWithPadding read len := by
  by_cases hz : len=0
  · simp only [hz, byteArray_readWithPadding_zero]
  have hpos : 0 < len := by omega
  have hleft : (mem.extract 0 off).size = off := by rw [ByteArray.size_extract]; omega
  have hword : (word.toByteArray.extract 0 32).size = 32 := by rw [ByteArray.size_extract, toByteArray_size]; omega
  have htail : (mem.extract (off+32) mem.size).size = mem.size-(off+32) := by rw [ByteArray.size_extract]; omega
  have hhead : (mem.extract 0 off ++ word.toByteArray.extract 0 32).size = off+32 := by
    rw [ByteArray.size_append, hleft, hword]
  rw [Reasoning.Theory.writeWord, write32_eq _ _ off (by rw [toByteArray_size]) (by omega)]
  rw [readWithPadding_eq_extract_unbounded _ read len hpos
    (by rw [ByteArray.size_append, hhead, htail]; omega),
    readWithPadding_eq_extract_unbounded mem read len hpos hin,
    extract_append_right_window _ _ _ _ (by rw [hhead]; omega), hhead, extract_extract_BA]
  rw [show off+32+(read-(off+32))=read by omega,
    show min (off+32+(read+len-(off+32))) mem.size=read+len by omega]

structure RecordArrayStepView (before after : ByteArray) (head base tail : UInt256) (a : AttestationRecord) : Prop where
  front : MemoryPrefix before after head.toNat
  headRead : after.readWithPadding head.toNat 32 = (recordArrayOffsetWord base tail).toByteArray
  recordRead : after.readWithPadding tail.toNat a.encoding.size = a.encoding
  covered : tail.toNat+a.encoding.size ≤ after.size
  gap : ∀ off words, head.toNat+32 ≤ off → off+32*words ≤ tail.toNat → off+32*words ≤ before.size →
    after.readWithPadding off (32*words) = before.readWithPadding off (32*words)

theorem recordArrayStepMemory_view (mem : ByteArray) (head base tail src dataPtr : UInt256) (a : AttestationRecord)
    (hv : AttestationMemoryView mem src dataPtr a)
    (hsrc : src.toNat+320 ≤ head.toNat)
    (hdata : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ head.toNat)
    (htail : head.toNat+32 ≤ tail.toNat)
    (hbound : tail.toNat+384+32*((a.data.size+31)/32) < UInt256.size) :
    RecordArrayStepView mem (recordArrayStepMemory mem head base tail src dataPtr) head base tail a := by
  let mid := Reasoning.Theory.writeWord mem head.toNat (recordArrayOffsetWord base tail)
  have hm : MemoryPrefix mem mid head.toNat := memoryPrefix_sparse_writeWord mem head.toNat head.toNat _ (Or.inl (le_refl _))
  have hv' : AttestationMemoryView mid src dataPtr a := hv.preserve hm hsrc hdata (by omega)
  have hp : MemoryPrefix mid (recordArrayStepMemory mem head base tail src dataPtr) tail.toNat :=
    attestationEncodedMemory_prefix mid src tail dataPtr a.data.size hv'.dataLow (by omega) hv'.dataCovered hv'.length hbound
  have hlo : 96 ≤ head.toNat := by have := hv.sourceLow; omega
  refine ⟨hm.trans (hp.mono (by omega)), ?_, ?_, ?_, ?_⟩
  · rw [memoryPrefix_read_words hp head.toNat 1 hlo (by omega) (by simp only [mid, writeWord_sparse_size]; omega) (by omega)]
    exact writeWord_sparse_read_back mem head.toNat (recordArrayOffsetWord base tail)
  · exact attestationRecordEncoded_read mid src tail dataPtr a hv'.dataLow (by omega) hv'.dataCovered
      hv'.length hv'.fields hv'.payload hbound
  · simpa only [a.encoding_size, Nat.add_assoc] using
      attestationEncodedMemory_covers mid src tail dataPtr a.data.size hv'.dataLow (by omega) hv'.dataCovered hv'.length hbound
  · intro off words hleft hright hin
    rw [memoryPrefix_read_words hp off words (by omega) hright (le_trans hin hm.size) (by omega)]
    exact writeWord_read_above_len mem head.toNat off (32*words) _ hleft hin

end Benchmarks.EAS.EAS
