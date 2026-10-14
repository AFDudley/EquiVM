import Benchmarks.EAS.EAS.RecordMemory
import Benchmarks.EAS.EAS.WordSequence
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def recordCreateMemory (mem : ByteArray) (src dataPtr : UInt256) (a : AttestationRecord) : ByteArray :=
  writeWordSequence mem src.toNat (a.words++[dataPtr])

theorem recordCreateMemory_load (mem : ByteArray) (src dataPtr : UInt256) (a : AttestationRecord)
    (i : Nat) (hi : i < 10) (hb : src.toNat+320 < UInt256.size) :
    memLoad (src+UInt256.ofNat (32*i)) (recordCreateMemory mem src dataPtr a) = (a.words++[dataPtr])[i]'(by exact hi) := by
  have he : src+UInt256.ofNat (32*i) = UInt256.ofNat (src.toNat+32*i) := by
    apply u256_inj
    rw [uadd_word_ofNat_toNat _ _ (by omega),ulit_toNat' _ (by omega)]
  rw [he]
  exact writeWordSequence_load_index mem src.toNat (a.words++[dataPtr]) i hi (by omega)

theorem recordCreateMemory_view {mem : ByteArray} {src dataPtr : UInt256} {a : AttestationRecord}
    (hlo : 96 ≤ src.toNat) (hdlo : 96 ≤ dataPtr.toNat)
    (hdata : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ src.toNat)
    (hin : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ mem.size)
    (hl : memLoad dataPtr mem = UInt256.ofNat a.data.size)
    (hr : mem.readWithPadding (dataPtr.toNat+32) a.data.size = a.data)
    (ht : a.time.toNat < 2^64) (he : a.expirationTime.toNat < 2^64) (hv : a.revocationTime.toNat < 2^64)
    (hb : src.toNat+320 < UInt256.size) :
    AttestationMemoryView (recordCreateMemory mem src dataPtr a) src dataPtr a := by
  have hp : MemoryPrefix mem (recordCreateMemory mem src dataPtr a) src.toNat :=
    writeWordSequence_prefix _ _ _ _ (le_refl _)
  have hc : src.toNat+320 ≤ (recordCreateMemory mem src dataPtr a).size :=
    writeWordSequence_covers mem src.toNat (a.words++[dataPtr]) (by simp [AttestationRecord.words])
  have hm (i : Nat) (hi : i < 10) := recordCreateMemory_load mem src dataPtr a i hi hb
  have h0 := hm 0 (by decide)
  simp only [Nat.mul_zero,show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,u256_add_zero] at h0
  refine ⟨hlo,hdlo,hc,le_trans hin hp.size,?_,?_,?_,?_⟩
  · exact hm 9 (by decide)
  · exact (memLoad_of_prefix hp dataPtr hdlo (by omega) (by omega)).trans hl
  · simp only [attestationEncodeHeadWords,attestationEncodeFirstWords,attestationEncodeLastWords,
      h0,hm 1 (by decide),hm 2 (by decide),hm 3 (by decide),hm 4 (by decide),hm 5 (by decide),
      hm 6 (by decide),hm 7 (by decide),hm 8 (by decide),AttestationRecord.words,List.cons_append,List.nil_append,
      List.getElem_cons_zero,List.getElem_cons_succ]
    rw [u256LandMaskCleanOfToNat (bits := 64) _ _ (by decide) ht,u256LandMaskCleanOfToNat (bits := 64) _ _ (by decide) he,
      u256LandMaskCleanOfToNat (bits := 64) _ _ (by decide) hv]
    have haddr (addr : AccountAddress) : UInt256.land (UInt256.ofNat addr.val) (UInt256.ofNat (2^160-1)) = UInt256.ofNat addr.val := by
      exact addressWord_val_clean addr
    rw [haddr,haddr]
    cases a.revocable <;> rfl
  · exact (memoryPrefix_read_prefix hp (dataPtr.toNat+32) ((a.data.size+31)/32) a.data.size
      (by omega) hdata hin (by omega) (by omega)).trans hr

end Benchmarks.EAS.EAS
