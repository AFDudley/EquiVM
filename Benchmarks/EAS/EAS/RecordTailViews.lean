import Benchmarks.EAS.EAS.RecordTailEVM
import Benchmarks.EAS.EAS.ArrayTripleStore
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem recordTailMemory_eq {mem : ByteArray} (site : UIDSite) (src t3 t4 value uidPtr word : UInt256)
    (i heap : Nat) (hsize : 96 ≤ mem.size)
    (ha : 96 ≤ (recordArrayPtr site t3 t4).toNat) (hv : 96 ≤ (recordValuesPtr site t4).toNat)
    (hu : 96 ≤ uidPtr.toNat) (hb : heap < UInt256.size) (hc : uidPtr.toNat+32+32*i < UInt256.size)
    (hh : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat heap) :
    recordTailMemory mem site src t3 t4 value uidPtr word i =
      arrayTripleStore mem uidPtr (recordArrayPtr site t3 t4) (recordValuesPtr site t4) heap i word src value := by
  have hn : (UInt256.ofNat (uidPtr.toNat+32+32*i)).toNat = uidPtr.toNat+32+32*i := ulit_toNat' _ hc
  have hf (m : ByteArray) (off : Nat) (w : UInt256) (hin : 96 ≤ m.size) (hlo : 96 ≤ off) :
      memLoad (UInt256.ofNat 64) (Reasoning.Theory.writeWord m off w) = memLoad (UInt256.ofNat 64) m :=
    memLoad_write_below m off _ w hlo hin
  have hfree : memLoad (UInt256.ofNat 64)
      (Reasoning.Theory.writeWord (recordSecondMemory mem site src t3 t4 value i) (uidPtr.toNat+32+32*i) word) =
      UInt256.ofNat heap := by
    unfold recordSecondMemory recordFirstMemory
    rw [hf _ _ word (by simp only [writeWord_sparse_size]; omega) (by omega),
      hf _ _ value (by simp only [writeWord_sparse_size]; omega) (by omega),hf _ _ src hsize (by omega),hh]
  unfold recordTailMemory recordEventMemory
  simp only [hn,hfree,ulit_toNat' _ hb]
  rfl

theorem recordTailMemory_views {mem : ByteArray} (site : UIDSite) {src t3 t4 value uidPtr word : UInt256}
    {ptrs values uids : List UInt256} {heap i : Nat}
    (ha : WordArrayMemoryView mem (recordArrayPtr site t3 t4) ptrs heap)
    (hv : WordArrayMemoryView mem (recordValuesPtr site t4) values heap)
    (hu : WordArrayMemoryView mem uidPtr uids heap)
    (hua : uidPtr.toNat+32+32*uids.length ≤ (recordArrayPtr site t3 t4).toNat)
    (hav : (recordArrayPtr site t3 t4).toNat+32+32*ptrs.length ≤ (recordValuesPtr site t4).toNat)
    (hia : i < ptrs.length) (hiv : i < values.length) (hiu : i < uids.length)
    (hb : heap < UInt256.size) (hh : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat heap) :
    WordArrayMemoryView (recordTailMemory mem site src t3 t4 value uidPtr word i) uidPtr (uids.set i word) heap ∧
    WordArrayMemoryView (recordTailMemory mem site src t3 t4 value uidPtr word i)
      (recordArrayPtr site t3 t4) (ptrs.set i src) heap ∧
    WordArrayMemoryView (recordTailMemory mem site src t3 t4 value uidPtr word i)
      (recordValuesPtr site t4) (values.set i value) heap ∧
    memLoad (UInt256.ofNat 64) (recordTailMemory mem site src t3 t4 value uidPtr word i) = UInt256.ofNat heap := by
  have hsize : 96 ≤ mem.size := by have := ha.covered; have := ha.low; omega
  rw [recordTailMemory_eq site src t3 t4 value uidPtr word i heap hsize ha.low hv.low hu.low hb
    (by have := hu.span; omega) hh]
  obtain ⟨hx,hy,hz⟩ := arrayTripleStore_views hu ha hv hua hav hiu hia hiv hb word src value
  exact ⟨hx,hy,hz,(arrayTripleStore_heap hsize hu.low ha.low hv.low (by have := ha.span; have := ha.low; omega) word src value).trans hh⟩

end Benchmarks.EAS.EAS
