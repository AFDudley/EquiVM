import Benchmarks.EAS.EAS.DefaultArrayAllocate
import Benchmarks.EAS.EAS.RecordCreateMemory
import Benchmarks.EAS.EAS.RecordDisjoint
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- GENERALIZES AttestationMemoryView.preserve to allocation interleaved with earlier pointer stores.
theorem AttestationMemoryView.structSlots_preserve {mem : ByteArray} {src dataPtr : UInt256}
    {a : AttestationRecord} (h : AttestationMemoryView mem src dataPtr a)
    (free slot : Nat) (fields : List UInt256) (n : Nat)
    (hs : src.toNat+320 ≤ free) (ht : slot+32*n ≤ src.toNat)
    (hd : dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ slot)
    (hb : src.toNat+320 < UInt256.size) :
    AttestationMemoryView (structSlotsMemory mem free slot fields n) src dataPtr a := by
  induction n generalizing mem free slot with
  | zero => exact h
  | succ n ih =>
    have hp : MemoryPrefix mem
        (wordSequenceMemory (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (free+32*fields.length))) free fields)
        (src.toNat+320) :=
      (memoryPrefix_sparse_writeWord _ 64 _ _ (Or.inr (by decide))).trans
        ((wordSequenceMemory_prefix _ free fields).mono hs)
    have hv := (h.preserve hp (le_refl _) (by omega) hb).write_disjoint slot (UInt256.ofNat free)
      hb (Or.inr (by omega)) (Or.inl hd)
    exact ih hv (free+32*fields.length) (slot+32) (by omega) (by omega) (by omega)

def defaultAttestationRecord : AttestationRecord :=
  ⟨⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0⟩,⟨0,by decide⟩,⟨0,by decide⟩,false,ByteArray.empty⟩

theorem defaultAttestationRecord_default :
    defaultValue? attestationType = .ok defaultAttestationRecord.value := by native_decide

theorem defaultAttestationSlotMemory_view (mem : ByteArray) (free slot : Nat)
    (hl : 128 ≤ slot) (hs : slot+32 ≤ free) (hb : free+320 < UInt256.size)
    (hin : 128 ≤ mem.size) (hz : memLoad (UInt256.ofNat 96) mem = ⟨0⟩) :
    AttestationMemoryView (structSlotMemory mem free slot defaultAttestationWords)
      (UInt256.ofNat free) (UInt256.ofNat 96) defaultAttestationRecord := by
  have hf : (UInt256.ofNat free).toNat = free := ulit_toNat' _ (by omega)
  have hp := memoryPrefix_sparse_writeWord mem 64 free (UInt256.ofNat (free+320)) (Or.inr (by decide))
  have hz' : memLoad (UInt256.ofNat 96) (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (free+320))) = ⟨0⟩ :=
    (memLoad_of_prefix hp (UInt256.ofNat 96) (by decide) (by change 128 ≤ free; omega) hin).trans hz
  have hv := recordCreateMemory_view (src := UInt256.ofNat free) (dataPtr := UInt256.ofNat 96)
    (a := defaultAttestationRecord) (by rw [hf]; omega) (by decide)
    (by change 128 ≤ (UInt256.ofNat free).toNat; rw [hf]; omega)
    (by change 128 ≤ (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (free+320))).size; exact le_trans hin hp.size)
    hz' (byteArray_readWithPadding_zero _ _) (by decide) (by decide) (by decide) (by rw [hf]; exact hb)
  have he : recordCreateMemory (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (free+320)))
      (UInt256.ofNat free) (UInt256.ofNat 96) defaultAttestationRecord =
      wordSequenceMemory (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (free+320))) free defaultAttestationWords := by
    unfold recordCreateMemory
    rw [hf]
    rfl
  rw [he] at hv
  exact hv.write_disjoint slot (UInt256.ofNat free) (by rw [hf]; exact hb)
    (Or.inr (by rw [hf]; exact hs)) (Or.inl hl)

theorem defaultAttestationSlotsMemory_view (mem : ByteArray) (free slot n i : Nat)
    (hl : 128 ≤ slot) (hs : slot+32*n ≤ free) (hb : free+320*n < UInt256.size)
    (hin : 128 ≤ mem.size) (hz : memLoad (UInt256.ofNat 96) mem = ⟨0⟩) (hi : i < n) :
    AttestationMemoryView (structSlotsMemory mem free slot defaultAttestationWords n)
      (UInt256.ofNat (free+320*i)) (UInt256.ofNat 96) defaultAttestationRecord := by
  induction n generalizing mem free slot i with
  | zero => omega
  | succ n ih =>
    have hlen : 32*defaultAttestationWords.length = 320 := rfl
    have hp := structSlotMemory_prefix mem free slot 128 defaultAttestationWords (by omega) hl
    have hz' : memLoad (UInt256.ofNat 96) (structSlotMemory mem free slot defaultAttestationWords) = ⟨0⟩ :=
      (memLoad_of_prefix hp (UInt256.ofNat 96) (by decide) (le_refl _) hin).trans hz
    cases i with
    | zero =>
      simp only [Nat.mul_zero,Nat.add_zero,structSlotsMemory,hlen]
      have hf : (UInt256.ofNat free).toNat = free := ulit_toNat' _ (by omega)
      exact (defaultAttestationSlotMemory_view mem free slot hl (by omega) (by omega) hin hz).structSlots_preserve
        (free+320) (slot+32) defaultAttestationWords n (by rw [hf]) (by rw [hf]; omega)
        (by change 128 ≤ slot+32; omega) (by rw [hf]; omega)
    | succ i =>
      have hv := ih (structSlotMemory mem free slot defaultAttestationWords) (free+320) (slot+32) i
        (by omega) (by omega) (by omega) (le_trans hin hp.size) hz' (by omega)
      simpa only [structSlotsMemory,hlen,Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hv

end Benchmarks.EAS.EAS
