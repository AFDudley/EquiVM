import Benchmarks.EAS.EAS.AttestRecordRegion
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem AttestRecordRegions.tail {mem : ByteArray} (site : UIDSite)
    {src dataPtr t3 t4 value uidPtr word : UInt256} {a : AttestationRecord}
    {ptrs values uids : List UInt256} {ats : List AttestationRecord} {heap i : Nat}
    (h : AttestRecordRegions mem uidPtr (recordArrayPtr site t3 t4) (recordValuesPtr site t4) ptrs ats heap)
    (hm : RecordTailMemoryView mem site t3 t4 uidPtr ptrs values uids value heap)
    (hv : AttestationMemoryView mem src dataPtr a) (hi : i < ptrs.length) (hb : heap < UInt256.size)
    (hs : src.toNat+320 ≤ heap) (hvalues : (recordValuesPtr site t4).toNat+32+32*values.length ≤ src.toNat)
    (hd : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ uidPtr.toNat) :
    AttestRecordRegions (recordTailMemory mem site src t3 t4 value uidPtr word i) uidPtr
      (recordArrayPtr site t3 t4) (recordValuesPtr site t4) (ptrs.set i src) (ats.set i a) heap := by
  have hu := hm.uidArray.span
  have hua := hm.uidRecords
  have hav := hm.recordValues
  have hvlen := hm.lengthValues
  have hiu : i < uids.length := by rw [hm.lengthUIDs]; exact hi
  have hiv : i < values.length := by rw [hm.lengthValues]; exact hi
  let final := recordTailMemory mem site src t3 t4 value uidPtr word i
  have hold : ∀ p b, AttestRecordRegion mem p b uidPtr.toNat
      ((recordArrayPtr site t3 t4).toNat+32+32*ptrs.length) (recordValuesPtr site t4).toNat
      ((recordValuesPtr site t4).toNat+32+32*ptrs.length) heap →
      AttestRecordRegion final p b uidPtr.toNat
      ((recordArrayPtr site t3 t4).toNat+32+32*ptrs.length) (recordValuesPtr site t4).toNat
      ((recordValuesPtr site t4).toNat+32+32*ptrs.length) heap := by
    intro p b hp
    have hps := hp.sourceStart
    have hpe := hp.sourceEnd
    have hpv := hp.valuesApart
    have hval : p.toNat+320 ≤ (recordValuesPtr site t4).toNat+32+32*i ∨
        (recordValuesPtr site t4).toNat+64+32*i ≤ p.toNat := by omega
    dsimp only [final]
    rw [recordTailMemory_eq site src t3 t4 value uidPtr word i heap
      (by have := hm.records.covered; have := hm.records.low; omega) hm.records.low hm.valueArray.low hm.uidArray.low hb
      (by omega) hm.heapRead]
    unfold arrayTripleStore
    exact (((hp.write _ src hb (by omega) (Or.inr (by omega))).write
      _ value hb (by omega) (by omega)).write
      _ word hb (by omega) (Or.inr (by omega))).write _ word hb (by omega) (Or.inl hpe)
  have hnew : AttestRecordRegion final src a uidPtr.toNat
      ((recordArrayPtr site t3 t4).toNat+32+32*ptrs.length) (recordValuesPtr site t4).toNat
      ((recordValuesPtr site t4).toNat+32+32*ptrs.length) heap :=
    ⟨hs,by omega,Or.inr (by omega),dataPtr,recordTailMemory_record site hm hv hi hb hs hvalues hd,hd⟩
  simpa only [AttestRecordRegions,List.length_set] using listForall₂_set (h.imp hold) i hnew

end Benchmarks.EAS.EAS
