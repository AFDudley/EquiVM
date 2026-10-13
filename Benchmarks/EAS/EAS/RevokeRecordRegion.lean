import Benchmarks.EAS.EAS.AttestRecordRegion
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- GENERALIZES AttestRecordRegion: copied payloads may lie after the two mutable array tables.
structure RevokeRecordRegion (mem : ByteArray) (src : UInt256) (a : AttestationRecord)
    (tableStart tableEnd valuesStart valuesEnd heap : Nat) : Prop where
  sourceEnd : src.toNat+320 ≤ heap
  sourceStart : tableEnd ≤ src.toNat
  valuesApart : src.toNat+320 ≤ valuesStart ∨ valuesEnd ≤ src.toNat
  view : ∃ dataPtr, AttestationMemoryView mem src dataPtr a ∧
    dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ heap ∧
    (dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ tableStart ∨ valuesEnd ≤ dataPtr.toNat)

theorem RevokeRecordRegion.preserve {before after : ByteArray} {src : UInt256} {a : AttestationRecord}
    {tableStart tableEnd valuesStart valuesEnd heap next : Nat}
    (h : RevokeRecordRegion before src a tableStart tableEnd valuesStart valuesEnd heap)
    (hp : MemoryPrefix before after heap) (hb : heap < UInt256.size) (hn : heap ≤ next) :
    RevokeRecordRegion after src a tableStart tableEnd valuesStart valuesEnd next := by
  obtain ⟨dp,hv,hd,ha⟩ := h.view
  exact ⟨le_trans h.sourceEnd hn,h.sourceStart,h.valuesApart,dp,hv.preserve hp h.sourceEnd hd hb,le_trans hd hn,ha⟩

theorem RevokeRecordRegion.write {mem : ByteArray} {src : UInt256} {a : AttestationRecord}
    {tableStart tableEnd valuesStart valuesEnd heap : Nat}
    (h : RevokeRecordRegion mem src a tableStart tableEnd valuesStart valuesEnd heap)
    (dst : Nat) (word : UInt256) (hb : heap < UInt256.size)
    (hd : (tableStart ≤ dst ∧ dst+32 ≤ tableEnd) ∨ (valuesStart ≤ dst ∧ dst+32 ≤ valuesEnd) ∨ heap ≤ dst)
    (ht : tableStart ≤ tableEnd ∧ tableEnd ≤ valuesStart ∧ valuesStart ≤ valuesEnd) :
    RevokeRecordRegion (Reasoning.Theory.writeWord mem dst word) src a tableStart tableEnd valuesStart valuesEnd heap := by
  obtain ⟨dp,hv,he,ha⟩ := h.view
  have hs := h.sourceEnd
  have hl := h.sourceStart
  have hvapart := h.valuesApart
  exact ⟨hs,hl,hvapart,dp,hv.write_disjoint dst word (by omega) (by omega) (by omega),he,ha⟩

def RevokeRecordRegions (mem : ByteArray) (array valuesPtr : UInt256)
    (ptrs : List UInt256) (ats : List AttestationRecord) (heap : Nat) : Prop :=
  List.Forall₂ (fun src a => RevokeRecordRegion mem src a array.toNat
    (array.toNat+32+32*ptrs.length) valuesPtr.toNat (valuesPtr.toNat+32+32*ptrs.length) heap) ptrs ats

theorem RevokeRecordRegions.preserve {before after : ByteArray} {array valuesPtr : UInt256}
    {ptrs : List UInt256} {ats : List AttestationRecord} {heap next : Nat}
    (h : RevokeRecordRegions before array valuesPtr ptrs ats heap)
    (hp : MemoryPrefix before after heap) (hb : heap < UInt256.size) (hn : heap ≤ next) :
    RevokeRecordRegions after array valuesPtr ptrs ats next := h.imp (fun _ _ hr => hr.preserve hp hb hn)

theorem RevokeRecordRegions.arrayView {mem : ByteArray} {array valuesPtr : UInt256}
    {ptrs : List UInt256} {ats : List AttestationRecord} {heap : Nat}
    (h : RevokeRecordRegions mem array valuesPtr ptrs ats heap) (hv : WordArrayMemoryView mem array ptrs heap) :
    AttestationArrayMemoryView mem array ats heap := by
  have hl := h.length_eq
  refine ⟨hv.low,?_,?_,?_,?_⟩
  · simpa only [← hl] using hv.span
  · simpa only [← hl] using hv.covered
  · simpa only [← hl] using hv.length
  · intro i hi
    have hj : i < ptrs.length := by omega
    have hr : RevokeRecordRegion mem ptrs[i] ats[i] array.toNat
        (array.toNat+32+32*ptrs.length) valuesPtr.toNat (valuesPtr.toNat+32+32*ptrs.length) heap := h.get hj hi
    obtain ⟨dp,hview,hd,_⟩ := hr.view
    exact ⟨ptrs[i],dp,hv.get i hj,hview,hr.sourceEnd,hd⟩

-- Default records have their empty payload before both output tables.
theorem AttestRecordRegions.toRevoke {mem : ByteArray} {uidPtr array valuesPtr : UInt256}
    {ptrs : List UInt256} {ats : List AttestationRecord} {heap : Nat}
    (h : AttestRecordRegions mem uidPtr array valuesPtr ptrs ats heap)
    (hu : uidPtr.toNat ≤ array.toNat) (hh : uidPtr.toNat ≤ heap) :
    RevokeRecordRegions mem array valuesPtr ptrs ats heap := by
  apply h.imp
  intro src a hr
  obtain ⟨dp,hv,hd⟩ := hr.view
  exact ⟨hr.sourceEnd,hr.sourceStart,hr.valuesApart,dp,hv,le_trans hd hh,Or.inl (le_trans hd hu)⟩

end Benchmarks.EAS.EAS
