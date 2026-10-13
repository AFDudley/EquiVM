import Benchmarks.EAS.EAS.ArrayDisjoint
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: update corresponding entries in three disjoint arrays and a scratch word.
def arrayTripleStore (mem : ByteArray) (first second third : UInt256) (heap i : Nat)
    (x y z : UInt256) : ByteArray :=
  let m1 := Reasoning.Theory.writeWord mem (second.toNat+32+32*i) y
  let m2 := Reasoning.Theory.writeWord m1 (third.toNat+32+32*i) z
  let m3 := Reasoning.Theory.writeWord m2 (first.toNat+32+32*i) x
  Reasoning.Theory.writeWord m3 heap x

theorem arrayTripleStore_views {mem : ByteArray} {first second third : UInt256}
    {xs ys zs : List UInt256} {heap i : Nat}
    (hx : WordArrayMemoryView mem first xs heap)
    (hy : WordArrayMemoryView mem second ys heap)
    (hz : WordArrayMemoryView mem third zs heap)
    (hxy : first.toNat+32+32*xs.length ≤ second.toNat)
    (hyz : second.toNat+32+32*ys.length ≤ third.toNat)
    (hix : i < xs.length) (hiy : i < ys.length) (hiz : i < zs.length)
    (hb : heap < UInt256.size) (x y z : UInt256) :
    WordArrayMemoryView (arrayTripleStore mem first second third heap i x y z) first (xs.set i x) heap ∧
    WordArrayMemoryView (arrayTripleStore mem first second third heap i x y z) second (ys.set i y) heap ∧
    WordArrayMemoryView (arrayTripleStore mem first second third heap i x y z) third (zs.set i z) heap := by
  have hx1 := hx.write_disjoint (second.toNat+32+32*i) y hb (Or.inl (by omega))
  have hy1 := hy.set i hiy y hb
  have hz1 := hz.write_disjoint (second.toNat+32+32*i) y hb (Or.inr (by omega))
  have hx2 := hx1.write_disjoint (third.toNat+32+32*i) z hb (Or.inl (by omega))
  have hy2 := hy1.write_disjoint (third.toNat+32+32*i) z hb (Or.inl (by simp only [List.length_set]; omega))
  have hz2 := hz1.set i hiz z hb
  have hx3 := hx2.set i hix x hb
  have hy3 := hy2.write_disjoint (first.toNat+32+32*i) x hb (Or.inr (by omega))
  have hz3 := hz2.write_disjoint (first.toNat+32+32*i) x hb (Or.inr (by omega))
  exact ⟨hx3.write_disjoint heap x hb (Or.inl hx3.span),
    hy3.write_disjoint heap x hb (Or.inl hy3.span),hz3.write_disjoint heap x hb (Or.inl hz3.span)⟩

theorem arrayTripleStore_heap {mem : ByteArray} {first second third : UInt256} {heap i : Nat}
    (hsize : 96 ≤ mem.size) (hx : 96 ≤ first.toNat) (hy : 96 ≤ second.toNat)
    (hz : 96 ≤ third.toNat) (hh : 96 ≤ heap) (x y z : UInt256) :
    memLoad (UInt256.ofNat 64) (arrayTripleStore mem first second third heap i x y z) =
      memLoad (UInt256.ofNat 64) mem := by
  unfold arrayTripleStore
  have hf (m : ByteArray) (off : Nat) (w : UInt256) (hin : 96 ≤ m.size) (hlo : 96 ≤ off) :
      memLoad (UInt256.ofNat 64) (Reasoning.Theory.writeWord m off w) = memLoad (UInt256.ofNat 64) m :=
    memLoad_write_below m off _ w hlo hin
  rw [hf _ heap x (by simp only [writeWord_sparse_size]; omega) hh,
    hf _ _ x (by simp only [writeWord_sparse_size]; omega) (by omega),
    hf _ _ z (by simp only [writeWord_sparse_size]; omega) (by omega),
    hf _ _ y hsize (by omega)]

end Benchmarks.EAS.EAS
