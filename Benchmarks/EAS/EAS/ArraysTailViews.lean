import Benchmarks.EAS.EAS.RecordArrayRead
import Benchmarks.EAS.EAS.EncodeValuesSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def resolverArraysBody (ats : List AttestationRecord) (values : List UInt256) : ByteArray :=
  wordBytes [UInt256.ofNat 64, UInt256.ofNat (64+(attestationArrayEncoding ats).size)] ++
    (attestationArrayEncoding ats ++ valuesEncoding values values.length)

def resolverArraysTailMemory (mem : ByteArray) (base : UInt256) (ats : List AttestationRecord) (values : List UInt256) : ByteArray :=
  writeWordSequence
    (Reasoning.Theory.writeWord mem (base.toNat+32) (UInt256.ofNat (64+(attestationArrayEncoding ats).size)))
    (recordArrayTail base ats ats.length) (UInt256.ofNat values.length::values)

theorem valuesEncoding_size (values : List UInt256) :
    (valuesEncoding values values.length).size = 32+32*values.length := by
  simp only [valuesEncoding, List.take_length, wordBytes_size, List.length_cons]
  omega

theorem resolverArraysBody_size (ats : List AttestationRecord) (values : List UInt256) :
    (resolverArraysBody ats values).size = 64+(attestationArrayEncoding ats).size+32+32*values.length := by
  simp only [resolverArraysBody, ByteArray.size_append, wordBytes_size, List.length_cons, List.length_nil, valuesEncoding_size]
  omega

theorem recordArrayTail_eq_encoding (base : UInt256) (ats : List AttestationRecord) :
    recordArrayTail base ats ats.length = base.toNat+64+(attestationArrayEncoding ats).size := by
  rw [attestationArrayEncoding_size]
  unfold recordArrayTail
  omega

theorem resolverArraysTailMemory_prefix (mem : ByteArray) (base : UInt256) (ats : List AttestationRecord)
    (values : List UInt256) (limit : Nat) (hbase : limit ≤ base.toNat) :
    MemoryPrefix mem (resolverArraysTailMemory mem base ats values) limit :=
  (memoryPrefix_sparse_writeWord mem (base.toNat+32) limit _ (Or.inl (by omega))).trans
    (writeWordSequence_prefix _ _ limit _ (by rw [recordArrayTail_eq_encoding]; omega))

theorem resolverArraysTailMemory_covers (mem : ByteArray) (base : UInt256) (ats : List AttestationRecord) (values : List UInt256) :
    base.toNat+(resolverArraysBody ats values).size ≤ (resolverArraysTailMemory mem base ats values).size := by
  have h := writeWordSequence_covers
    (Reasoning.Theory.writeWord mem (base.toNat+32) (UInt256.ofNat (64+(attestationArrayEncoding ats).size)))
    (recordArrayTail base ats ats.length) (UInt256.ofNat values.length::values) (by simp)
  simp only [List.length_cons, recordArrayTail_eq_encoding, resolverArraysBody_size] at h ⊢
  simp only [resolverArraysTailMemory, recordArrayTail_eq_encoding]
  omega

theorem resolverArraysTailMemory_read {before mem : ByteArray} {base : UInt256}
    {ats : List AttestationRecord} {limit : Nat} (values : List UInt256)
    (h : RecordArrayLoopView before mem base ats limit ats.length) :
    (resolverArraysTailMemory mem base ats values).readWithPadding base.toNat (resolverArraysBody ats values).size =
      resolverArraysBody ats values := by
  let mid := Reasoning.Theory.writeWord mem (base.toNat+32) (UInt256.ofNat (64+(attestationArrayEncoding ats).size))
  let out := resolverArraysTailMemory mem base ats values
  have hc := h.final_covered
  rw [recordArrayTail_eq_encoding] at hc
  have h64 : base.toNat+64 ≤ mem.size := by have hh := h.headsCovered; unfold recordArrayHead at hh; omega
  have hfirst : out.readWithPadding base.toNat 32 = (UInt256.ofNat 64).toByteArray := by
    rw [show out = writeWordSequence mid (recordArrayTail base ats ats.length) (UInt256.ofNat values.length::values) from rfl,
      writeWordSequence_read_below _ _ base.toNat _ (by simp only [mid, writeWord_sparse_size]; omega)
        (by rw [recordArrayTail_eq_encoding]; omega),
      show mid = Reasoning.Theory.writeWord mem (base.toNat+32) (UInt256.ofNat (64+(attestationArrayEncoding ats).size)) from rfl,
      writeWord_sparse_read_preserved _ _ _ _ (Or.inl ⟨by omega, by omega⟩)]
    exact h.baseOffset
  have hsecond : out.readWithPadding (base.toNat+32) 32 = (UInt256.ofNat (64+(attestationArrayEncoding ats).size)).toByteArray := by
    rw [show out = writeWordSequence mid (recordArrayTail base ats ats.length) (UInt256.ofNat values.length::values) from rfl,
      writeWordSequence_read_below _ _ (base.toNat+32) _ (by simp only [mid, writeWord_sparse_size]; omega)
        (by rw [recordArrayTail_eq_encoding]; omega)]
    exact writeWord_sparse_read_back _ _ _
  have hrecord : out.readWithPadding (base.toNat+64) (attestationArrayEncoding ats).size = attestationArrayEncoding ats := by
    rw [show out = writeWordSequence mid (recordArrayTail base ats ats.length) (UInt256.ofNat values.length::values) from rfl,
      writeWordSequence_read_below_len _ _ (base.toNat+64) (attestationArrayEncoding ats).size _
        (by rw [recordArrayTail_eq_encoding]) (by simp only [mid, writeWord_sparse_size]; omega),
      show mid = Reasoning.Theory.writeWord mem (base.toNat+32) (UInt256.ofNat (64+(attestationArrayEncoding ats).size)) from rfl,
      writeWord_read_above_len _ _ _ _ _ (by omega) hc]
    exact h.record_read
  have hvalues : out.readWithPadding (recordArrayTail base ats ats.length) (valuesEncoding values values.length).size =
      valuesEncoding values values.length := by
    simpa only [out, resolverArraysTailMemory, valuesEncoding, List.take_length, wordBytes_size] using
      writeWordSequence_read mid (recordArrayTail base ats ats.length) (UInt256.ofNat values.length::values)
  have hcover : base.toNat+64+(attestationArrayEncoding ats).size+(valuesEncoding values values.length).size ≤ out.size := by
    have hh := resolverArraysTailMemory_covers mem base ats values
    simp only [resolverArraysBody_size, valuesEncoding_size, out] at hh ⊢
    omega
  have hheads := readWithPadding_concat out base.toNat (UInt256.ofNat 64).toByteArray
    (UInt256.ofNat (64+(attestationArrayEncoding ats).size)).toByteArray
    (by rw [toByteArray_size]; exact hfirst) (by rw [toByteArray_size, toByteArray_size]; exact hsecond)
    (by rw [toByteArray_size, toByteArray_size]; omega)
  have hheads' : out.readWithPadding base.toNat (wordBytes [UInt256.ofNat 64, UInt256.ofNat (64+(attestationArrayEncoding ats).size)]).size =
      wordBytes [UInt256.ofNat 64, UInt256.ofNat (64+(attestationArrayEncoding ats).size)] := by
    simpa only [wordBytes, ByteArray.append_empty, ByteArray.size_append] using hheads
  have ht := readWithPadding_concat out (base.toNat+64) (attestationArrayEncoding ats) (valuesEncoding values values.length)
    hrecord (by rw [← recordArrayTail_eq_encoding]; exact hvalues) hcover
  have ht' : out.readWithPadding (base.toNat+64) (attestationArrayEncoding ats ++ valuesEncoding values values.length).size =
      attestationArrayEncoding ats ++ valuesEncoding values values.length := by
    simpa only [ByteArray.size_append] using ht
  have hhsize : (wordBytes [UInt256.ofNat 64, UInt256.ofNat (64+(attestationArrayEncoding ats).size)]).size = 64 := by
    rw [wordBytes_size]
    rfl
  have hr := readWithPadding_concat out base.toNat
    (wordBytes [UInt256.ofNat 64, UInt256.ofNat (64+(attestationArrayEncoding ats).size)])
    (attestationArrayEncoding ats ++ valuesEncoding values values.length)
    hheads' (by rw [hhsize]; exact ht') (by rw [hhsize, ByteArray.size_append]; omega)
  simpa only [out, resolverArraysBody, ByteArray.size_append] using hr

end Benchmarks.EAS.EAS
