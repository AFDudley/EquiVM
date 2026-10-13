import Benchmarks.EAS.EAS.RevokePublicControl
import Benchmarks.EAS.EAS.RevokeDecode
import Benchmarks.EAS.EAS.RevocationRequestMemory
import Benchmarks.EAS.EAS.RecordUID
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem revokePublicInputMemory_view (cd : ByteArray) :
    RevocationRequestArrayMemoryView (revokePublicInputMemory cd) (UInt256.ofNat 224)
      [revocationDataRecord cd 36] 416 ∧
    memLoad (UInt256.ofNat 64) (revokePublicInputMemory cd) = UInt256.ofNat 416 ∧
    memLoad (UInt256.ofNat 96) (revokePublicInputMemory cd) = ⟨0⟩ := by
  have hc : (revokePublicCopiedMemory cd).size = 416 := by
    simp only [revokePublicCopiedMemory,writeWord_sparse_size,revokePublicArrayMemory_facts.1,Nat.reduceAdd]
    decide
  have hi : (revokePublicInputMemory cd).size = 416 := by
    simp only [revokePublicInputMemory,writeWord_sparse_size,hc,Nat.reduceAdd]
    decide
  have hp : MemoryPrefix revokePublicArrayMemory (revokePublicInputMemory cd) 256 := by
    have h1 := memoryPrefix_sparse_writeWord revokePublicArrayMemory 64 256 (UInt256.ofNat 416) (Or.inr (by decide))
    have h2 := writeWordSequence_prefix (Reasoning.Theory.writeWord revokePublicArrayMemory 64 (UInt256.ofNat 416))
      352 256 [calldataWord cd 36,calldataWord cd 68] (by decide)
    exact (h1.trans h2).trans (memoryPrefix_sparse_writeWord (revokePublicCopiedMemory cd) 256 256 (UInt256.ofNat 352) (Or.inl (le_refl _)))
  have hread (i : Nat) (hb : i < 2) :
      memLoad (UInt256.ofNat (352+32*i)) (revokePublicInputMemory cd) = [calldataWord cd 36,calldataWord cd 68][i] := by
    unfold revokePublicInputMemory
    rw [memLoad_write_above _ _ _ _
      (by rw [ulit_toNat' _ (by change 352+32*i < 2^256; omega)]; omega)
      (by rw [ulit_toNat' _ (by change 352+32*i < 2^256; omega),hc]; omega)]
    exact writeWordSequence_load_index _ 352 [calldataWord cd 36,calldataWord cd 68] i hb
      (by change 352+32*i < 2^256; omega)
  have hptr : memLoad (UInt256.ofNat 256) (revokePublicInputMemory cd) = UInt256.ofNat 352 :=
    writeWordSequence_load_index (revokePublicCopiedMemory cd) 256 [UInt256.ofNat 352] 0 (by decide) (by decide)
  have hf : memLoad (UInt256.ofNat 64) (revokePublicCopiedMemory cd) = UInt256.ofNat 416 :=
    writeWordSequence_setFree_load64 revokePublicArrayMemory 352 [calldataWord cd 36,calldataWord cd 68] (UInt256.ofNat 416) (by decide)
  refine ⟨?_,?_,?_⟩
  · refine ⟨by decide,by change 288 ≤ 416; decide,by rw [hi]; change 288 ≤ 416; decide,?_,?_⟩
    · exact (memLoad_of_prefix hp (UInt256.ofNat 224) (by decide) (by decide)
        (by rw [revokePublicArrayMemory_facts.1]; decide)).trans revokePublicArrayMemory_facts.2.1
    · intro i hb
      have hz : i = 0 := by simpa only [List.length_singleton,Nat.lt_one_iff] using hb
      subst i
      refine ⟨UInt256.ofNat 352,hptr,?_,by decide⟩
      exact ⟨by decide,by rw [hi]; decide,hread 0 (by decide),hread 1 (by decide)⟩
  · exact (memLoad_write_below _ _ _ _ (by decide) (by rw [hc]; decide)).trans hf
  · exact (memLoad_of_prefix hp (UInt256.ofNat 96) (by decide) (by decide)
      (by rw [revokePublicArrayMemory_facts.1]; decide)).trans revokePublicArrayMemory_facts.2.2.2

end Benchmarks.EAS.EAS
