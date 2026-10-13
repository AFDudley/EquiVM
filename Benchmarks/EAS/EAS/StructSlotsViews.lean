import Benchmarks.EAS.Attester.StructAllocMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: each initialized pointer slot addresses its corresponding fixed-width struct.
theorem structSlotsMemory_slot (mem : ByteArray) (free slot : Nat) (fields : List UInt256) (n i : Nat)
    (hlo : 96 ≤ slot) (hslots : slot+32*n ≤ free) (hfit : slot+32*n < UInt256.size) (hi : i < n) :
    memLoad (UInt256.ofNat (slot+32*i)) (structSlotsMemory mem free slot fields n) =
      UInt256.ofNat (free+32*fields.length*i) := by
  induction n generalizing mem free slot i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero =>
      simp only [Nat.mul_zero,Nat.add_zero,structSlotsMemory]
      let m := structSlotMemory mem free slot fields
      have hp := structSlotsMemory_prefix m (free+32*fields.length) (slot+32) (slot+32) fields
        (by omega) (le_refl _) n
      have hin : slot+32 ≤ m.size := by
        dsimp only [m,structSlotMemory]
        rw [writeWord_sparse_size]
        exact Nat.le_max_right _ _
      have hl : memLoad (UInt256.ofNat slot) m = UInt256.ofNat free := by
        unfold m structSlotMemory
        exact memLoad_write_same _ _ _ _ (ulit_toNat' _ (by omega))
      exact (hp.load_preserved hlo (le_refl _) hin (by omega)).trans hl
    | succ i =>
      have h := ih (structSlotMemory mem free slot fields) (free+32*fields.length) (slot+32) i
        (by omega) (by omega) (by omega) (by omega)
      simpa only [structSlotsMemory,Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

end Benchmarks.EAS.EAS
