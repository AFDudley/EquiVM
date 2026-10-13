import Benchmarks.EAS.EAS.ArrayTablePreserve
import Benchmarks.EAS.EAS.MultiAttestFacts
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

structure MultiAttestMemory (mem : ByteArray) (table : UInt256)
    (groups : List (List UInt256)) (i heap : Nat) : Prop where
  view : WordArrayTablePrefix mem table groups i heap
  low : 224≤table.toNat
  empty : EmptyArraySuffix groups i
  free : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat heap
  zero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩

theorem MultiAttestMemory.preserve {mem after : ByteArray} {table : UInt256}
    {groups : List (List UInt256)} {i heap next : Nat}
    (h : MultiAttestMemory mem table groups i heap) (hp : MemoryPrefix mem after heap)
    (hle : heap≤next) (hb : next<UInt256.size)
    (hf : memLoad (UInt256.ofNat 64) after = UInt256.ofNat next) :
    MultiAttestMemory after table groups i next := by
  refine ⟨h.view.preserve hp hle hb,h.low,h.empty,hf,?_⟩
  exact (memLoad_of_prefix hp (UInt256.ofNat 96) (by decide)
    (by change 128≤heap; have := h.view.span; have := h.low; omega)
    (by change 128≤mem.size; have := h.view.covered; have := h.low; omega)).trans h.zero

theorem MultiAttestMemory.set {mem : ByteArray} {table uid : UInt256}
    {groups : List (List UInt256)} {words : List UInt256} {i heap : Nat}
    (h : MultiAttestMemory mem table groups i heap) (hi : i<groups.length)
    (hu : WordArrayMemoryView mem uid words heap) (hl : table.toNat+32+32*groups.length≤uid.toNat)
    (hb : heap<UInt256.size) :
    MultiAttestMemory (Reasoning.Theory.writeWord mem (table.toNat+32+32*i) uid)
      table (groups.set i words) (i+1) heap := by
  refine ⟨h.view.set hi hu hl hb,h.low,h.empty.set words,?_,?_⟩
  · exact (memLoad_write_below _ _ (UInt256.ofNat 64) _
      (by change 96≤_; have := h.low; omega)
      (by change 96≤mem.size; have := h.view.covered; have := h.low; omega)).trans h.free
  · exact (memLoad_write_below _ _ (UInt256.ofNat 96) _
      (by change 128≤_; have := h.low; omega)
      (by change 128≤mem.size; have := h.view.covered; have := h.low; omega)).trans h.zero

theorem MultiAttestMemory.flatten_fit {mem : ByteArray} {table : UInt256}
    {groups : List (List UInt256)} {i heap : Nat} (h : MultiAttestMemory mem table groups i heap)
    (hb : heap≤2^64-1) : groups.flatten.length<UInt256.size := by
  have hlen : groups.length≤2^64-1 := by have := h.view.span; omega
  have ht := flattenLength_le groups (2^64-1) (by
    intro xs hx
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hx
    by_cases hji : j < i
    · obtain ⟨p,hptr,hv,hlo⟩ := h.view.arrays j hji
      have hs := hv.span
      rw [he] at hs
      omega
    · have hz := h.empty j hj (by omega)
      rw [he] at hz
      rw [hz,List.length_nil]
      omega)
  have hm := Nat.mul_le_mul_right (2^64-1) hlen
  change _<2^256
  omega

theorem multiAttestReturnedMemory {before after : ByteArray} {table heap data attester used : UInt256}
    {groups : List (List UInt256)} {words : List UInt256} {rs : List AttestationRequestRecord} {i next : Nat}
    (h : MultiAttestMemory before table groups i heap.toNat) (hh : heap.toNat≤2^64-1)
    (hd : AttestationRequestArrayRegion before data rs 224 heap.toNat)
    (hp : MemoryPrefix (attestAllocationMemory .many before heap data attester) after heap.toNat)
    (hv : AttestResultMemoryView after (UInt256.ofNat (allocateNext heap.toNat 64))
      (UInt256.ofNat (allocateNext heap.toNat 128)) words used next)
    (hle : heap.toNat≤next) (hb : next≤2^64-1)
    (hf : memLoad (UInt256.ofNat 64) after = UInt256.ofNat next) :
    MultiAttestMemory after table groups i next ∧
      table.toNat+32+32*groups.length≤(UInt256.ofNat (allocateNext heap.toNat 64)).toNat := by
  have hu : (UInt256.ofNat (allocateNext heap.toNat 128)).toNat = allocateNext heap.toNat 128 :=
    ulit_toNat' _ (by rw [allocateNext_128 hh]; change _<2^256; omega)
  have hn : allocateNext heap.toNat 128≤2^64-1 := by
    have hs := hv.uids.span
    rw [hu] at hs
    omega
  have hview := attestAllocationMemory_table (data := data) .many attester h.view h.low hh hn
  have hcover : 224≤before.size := by have := h.view.covered; have := h.low; omega
  have hdata := hd.view.span
  have hdcov := hd.view.covered
  have hlow := hd.arrayLow
  have hfree : memLoad (UInt256.ofNat 64) before = heap := by simpa only [u256_ofNat_toNat] using h.free
  have hm := attestAllocationMemory_facts .many before heap data attester hcover hlow
    (by omega) (by omega) hh hfree h.zero hn
  refine ⟨?_,le_trans h.view.span hm.2.1⟩
  refine ⟨hview.preserve hp hle (by change _<2^256; omega),h.low,h.empty,hf,?_⟩
  exact (memLoad_of_prefix hp (UInt256.ofNat 96) (by decide)
    (by change 128≤heap.toNat; have := h.view.span; have := h.low; omega)
    (by change 128≤_; have := hview.covered; have := h.low; omega)).trans hm.2.2.2.2.2.1

end Benchmarks.EAS.EAS
