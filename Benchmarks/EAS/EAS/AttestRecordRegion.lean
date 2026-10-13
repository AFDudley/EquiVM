import Benchmarks.EAS.EAS.RecordTailRecord
import Benchmarks.EAS.EAS.RecordArrayMemory
import Mathlib.Data.List.Forall2
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: simultaneous replacement preserves a pointwise relation between two lists.
theorem listForall₂_set {α β : Type*} {rel : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ rel xs ys) (i : Nat) {x : α} {y : β} (hxy : rel x y) :
    List.Forall₂ rel (xs.set i x) (ys.set i y) := by
  induction h generalizing i with
  | nil => exact List.Forall₂.nil
  | cons hxy0 hrest ih =>
    cases i with
    | zero => exact List.Forall₂.cons hxy hrest
    | succ i => exact List.Forall₂.cons hxy0 (ih i)

structure AttestRecordRegion (mem : ByteArray) (src : UInt256) (a : AttestationRecord)
    (uidStart tableEnd valuesStart valuesEnd heap : Nat) : Prop where
  sourceEnd : src.toNat+320 ≤ heap
  sourceStart : tableEnd ≤ src.toNat
  valuesApart : src.toNat+320 ≤ valuesStart ∨ valuesEnd ≤ src.toNat
  view : ∃ dataPtr, AttestationMemoryView mem src dataPtr a ∧
    dataPtr.toNat+32+32*((a.data.size+31)/32) ≤ uidStart

theorem AttestRecordRegion.preserve {before after : ByteArray} {src : UInt256} {a : AttestationRecord}
    {uidStart tableEnd valuesStart valuesEnd heap next : Nat}
    (h : AttestRecordRegion before src a uidStart tableEnd valuesStart valuesEnd heap)
    (hp : MemoryPrefix before after heap) (hb : heap < UInt256.size) (hu : uidStart ≤ heap) (hn : heap ≤ next) :
    AttestRecordRegion after src a uidStart tableEnd valuesStart valuesEnd next := by
  obtain ⟨dp,hv,hd⟩ := h.view
  exact ⟨le_trans h.sourceEnd hn,h.sourceStart,h.valuesApart,dp,
    hv.preserve hp h.sourceEnd (le_trans hd hu) hb,hd⟩

theorem AttestRecordRegion.write {mem : ByteArray} {src : UInt256} {a : AttestationRecord}
    {uidStart tableEnd valuesStart valuesEnd heap : Nat}
    (h : AttestRecordRegion mem src a uidStart tableEnd valuesStart valuesEnd heap)
    (dst : Nat) (word : UInt256) (hb : heap < UInt256.size)
    (hd : uidStart ≤ dst) (hs : src.toNat+320 ≤ dst ∨ dst+32 ≤ src.toNat) :
    AttestRecordRegion (Reasoning.Theory.writeWord mem dst word) src a uidStart tableEnd valuesStart valuesEnd heap := by
  obtain ⟨dp,hv,he⟩ := h.view
  exact ⟨h.sourceEnd,h.sourceStart,h.valuesApart,dp,
    hv.write_disjoint dst word (by have := h.sourceEnd; omega) hs (Or.inl (le_trans he hd)),he⟩

def AttestRecordRegions (mem : ByteArray) (uidPtr array valuesPtr : UInt256)
    (ptrs : List UInt256) (ats : List AttestationRecord) (heap : Nat) : Prop :=
  List.Forall₂ (fun src a => AttestRecordRegion mem src a uidPtr.toNat
    (array.toNat+32+32*ptrs.length) valuesPtr.toNat (valuesPtr.toNat+32+32*ptrs.length) heap) ptrs ats

theorem AttestRecordRegions.preserve {before after : ByteArray} {uidPtr array valuesPtr : UInt256}
    {ptrs : List UInt256} {ats : List AttestationRecord} {heap next : Nat}
    (h : AttestRecordRegions before uidPtr array valuesPtr ptrs ats heap)
    (hp : MemoryPrefix before after heap) (hb : heap < UInt256.size) (hu : uidPtr.toNat ≤ heap) (hn : heap ≤ next) :
    AttestRecordRegions after uidPtr array valuesPtr ptrs ats next :=
  h.imp (fun _ _ hr => hr.preserve hp hb hu hn)

theorem AttestRecordRegions.arrayView {mem : ByteArray} {uidPtr array valuesPtr : UInt256}
    {ptrs : List UInt256} {ats : List AttestationRecord} {heap : Nat}
    (h : AttestRecordRegions mem uidPtr array valuesPtr ptrs ats heap)
    (hv : WordArrayMemoryView mem array ptrs heap) (hu : uidPtr.toNat ≤ heap) :
    AttestationArrayMemoryView mem array ats heap := by
  have hl := h.length_eq
  refine ⟨hv.low,?_,?_,?_,?_⟩
  · simpa only [← hl] using hv.span
  · simpa only [← hl] using hv.covered
  · simpa only [← hl] using hv.length
  · intro i hi
    have hj : i < ptrs.length := by omega
    have hr : AttestRecordRegion mem ptrs[i] ats[i] uidPtr.toNat
        (array.toNat+32+32*ptrs.length) valuesPtr.toNat (valuesPtr.toNat+32+32*ptrs.length) heap := h.get hj hi
    obtain ⟨dp,hview,hd⟩ := hr.view
    exact ⟨ptrs[i],dp,hv.get i hj,hview,hr.sourceEnd,le_trans hd hu⟩

end Benchmarks.EAS.EAS
