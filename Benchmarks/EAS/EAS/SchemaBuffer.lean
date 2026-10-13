import Benchmarks.EAS.EAS.ReturnMemory
import Benchmarks.EAS.EAS.SchemaFields
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: read a buffer word at an equivalent EVM memory address.
theorem ReturnMemoryView.load {mem out : ByteArray} {base i : Nat} {ptr : UInt256}
    (h : ReturnMemoryView mem base out) (hp : ptr.toNat = base+i) (hi : i+32 ≤ out.size) :
    memLoad ptr mem = calldataWord out i := by
  rw [← u256_ofNat_toNat ptr,hp]
  exact h.words i hi

-- LIBRARY CANDIDATE: canonical Boolean words have the same natural and EVM tests.
theorem boolWord_nat_iff (w : UInt256) :
    (w=⟨0⟩ ∨ w=⟨1⟩) ↔ (w.toNat=0 ∨ w.toNat=1) := by
  constructor
  · rintro (h|h) <;> subst w <;> decide
  · rintro (h|h)
    · exact Or.inl (u256_inj h)
    · exact Or.inr (u256_inj h)

theorem boolWord_from_nat (w : UInt256) (h : w.toNat=0 ∨ w.toNat=1) :
    UInt256.fromBool (decide (w.toNat≠0)) = w := by
  rcases (boolWord_nat_iff w).mpr h with h|h <;> subst w <;> rfl

theorem schemaFieldsMemory_heap (mem : ByteArray) (src dst next : UInt256) (hlo : 96 ≤ dst.toNat) :
    memLoad (UInt256.ofNat 64) (schemaFieldsMemory (Reasoning.Theory.writeWord mem 64 next) src dst) = next :=
  writeWordSequence_setFree_load64 _ _ _ _ hlo

end Benchmarks.EAS.EAS
