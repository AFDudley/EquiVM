import Benchmarks.EAS.EAS.SchemaFields
import Benchmarks.EAS.EAS.SchemaTextMemory
import Benchmarks.EAS.EAS.ReturnMemory
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

structure SchemaMemoryView (mem : ByteArray) (ptr : UInt256) (a : SchemaRecord) : Prop where
  low : 96 ≤ ptr.toNat
  covered : ptr.toNat+128 ≤ mem.size
  uid : memLoad ptr mem = a.uid
  resolver : memLoad (ptr+UInt256.ofNat 32) mem = UInt256.ofNat a.resolver.toNat
  revocable : memLoad (ptr+UInt256.ofNat 64) mem = UInt256.fromBool a.revocable

theorem SchemaMemoryView.preserve {before after : ByteArray} {ptr : UInt256} {a : SchemaRecord} {limit : Nat}
    (h : SchemaMemoryView before ptr a) (hp : MemoryPrefix before after limit)
    (hh : ptr.toNat+128 ≤ limit) (hb : limit < UInt256.size) : SchemaMemoryView after ptr a := by
  have keep (n : Nat) (hn : n ≤ 64) : memLoad (ptr+UInt256.ofNat n) after = memLoad (ptr+UInt256.ofNat n) before := by
    have hx := uadd_word_ofNat_toNat ptr n (by omega)
    exact memLoad_of_prefix hp _ (by rw [hx]; have := h.low; omega) (by rw [hx]; omega)
      (by rw [hx]; have := h.covered; omega)
  refine ⟨h.low,le_trans h.covered hp.size,?_,?_,?_⟩
  · have hk := keep 0 (by decide)
    simp only [show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,u256_add_zero] at hk
    exact hk.trans h.uid
  · exact (keep 32 (by decide)).trans h.resolver
  · exact (keep 64 (by decide)).trans h.revocable

theorem schemaFieldsMemory_load (mem : ByteArray) (src dst : UInt256) (i : Nat) (hi : i < 3)
    (hb : dst.toNat+96 < UInt256.size) :
    memLoad (dst+UInt256.ofNat (32*i)) (schemaFieldsMemory mem src dst) = memLoad (src+UInt256.ofNat (32*i)) mem := by
  have hptr : dst+UInt256.ofNat (32*i) = UInt256.ofNat (dst.toNat+32*i) := by
    apply u256_inj
    rw [uadd_word_ofNat_toNat _ _ (by omega),ulit_toNat' _ (by omega)]
  rw [hptr]
  have h := writeWordSequence_load_index mem dst.toNat
    [memLoad src mem,memLoad (src+UInt256.ofNat 32) mem,memLoad (src+UInt256.ofNat 64) mem] i hi (by omega)
  interval_cases i <;> simpa only [schemaFieldsMemory, List.getElem_cons_zero,List.getElem_cons_succ,
    Nat.mul_zero,Nat.mul_one,Nat.reduceMul,show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,u256_add_zero] using h

theorem schemaFieldsMemory_prefix (mem : ByteArray) (src dst : UInt256) :
    MemoryPrefix mem (schemaFieldsMemory mem src dst) dst.toNat :=
  writeWordSequence_prefix _ _ _ _ (le_refl _)

theorem schemaFieldsMemory_covers (mem : ByteArray) (src dst : UInt256) :
    dst.toNat+96 ≤ (schemaFieldsMemory mem src dst).size :=
  writeWordSequence_covers mem dst.toNat
    [memLoad src mem,memLoad (src+UInt256.ofNat 32) mem,memLoad (src+UInt256.ofNat 64) mem] (by simp)

theorem schemaFieldsTextMemory_views (mem : ByteArray) (src dst text heap len : UInt256)
    (a : SchemaRecord) (hlo : 96 ≤ dst.toNat) (hdisj : dst.toNat+128 ≤ heap.toNat)
    (hh : heap.toNat ≤ 2^64-1) (hl : len.toNat ≤ 2^64-1)
    (hu : memLoad src mem = a.uid)
    (ha : memLoad (src+UInt256.ofNat 32) mem = UInt256.ofNat a.resolver.toNat)
    (hr : memLoad (src+UInt256.ofNat 64) mem = UInt256.fromBool a.revocable) :
    let final := schemaTextMemory (schemaFieldsMemory mem src dst) text heap dst len
    MemoryPrefix mem final dst.toNat ∧ SchemaMemoryView final dst a ∧
    memLoad (UInt256.ofNat 64) final = UInt256.ofNat (allocateNext heap.toNat (bytesAllocation len.toNat)) := by
  have ht := schemaTextMemory_views (schemaFieldsMemory mem src dst) text heap dst len hlo hdisj hh hl
  have hc := schemaFieldsMemory_covers mem src dst
  have hb : dst.toNat+128 < UInt256.size := by change dst.toNat+128 < 2^256; omega
  have keep (n : Nat) (hn : n ≤ 64) :
      memLoad (dst+UInt256.ofNat n) (schemaTextMemory (schemaFieldsMemory mem src dst) text heap dst len) =
      memLoad (dst+UInt256.ofNat n) (schemaFieldsMemory mem src dst) := by
    have hx := uadd_word_ofNat_toNat dst n (by omega)
    exact memLoad_of_prefix ht.1 _ (by rw [hx]; omega) (by rw [hx]; omega) (by rw [hx]; omega)
  refine ⟨(schemaFieldsMemory_prefix mem src dst).trans (ht.1.mono (by omega)),?_,ht.2.1⟩
  refine ⟨hlo,ht.2.2,?_,?_,?_⟩
  · have h := (keep 0 (by decide)).trans (schemaFieldsMemory_load mem src dst 0 (by decide) (by omega))
    simp only [Nat.mul_zero,show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl,u256_add_zero] at h
    exact h.trans hu
  · exact (keep 32 (by decide)).trans ((schemaFieldsMemory_load mem src dst 1 (by decide) (by omega)).trans ha)
  · exact (keep 64 (by decide)).trans ((schemaFieldsMemory_load mem src dst 2 (by decide) (by omega)).trans hr)

end Benchmarks.EAS.EAS
