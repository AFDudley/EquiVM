import Benchmarks.EAS.EAS.DelegatedRevocationDataMemory
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem delegatedRevocationAssembleMemory {mem : ByteArray} {row data sig : UInt256}
    {r : DelegatedRevocationBatch} {heap : Nat}
    (hd : DelegatedRevocationDataMemoryView mem row data r.schema r.data heap)
    (hs : CopySignatureArrayMemory mem sig r.signatures r.signatures.length heap)
    (hsep : row.toNat+128 ≤ sig.toNat) (hh : heap < UInt256.size)
    (hf : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat heap) :
    let final := delegatedRevocationSetRevoker (delegatedRevocationLinkSignatures mem row sig) row (UInt256.ofNat r.revoker.val)
    DelegatedRevocationBatchMemoryView final row data sig r heap ∧
    memLoad (UInt256.ofNat 64) final = UInt256.ofNat heap ∧ MemoryPrefix mem final row.toNat := by
  have hlo := hd.low
  have hc := hd.covered
  have hb := hd.data.span
  have hds := hd.separation
  have hss := hs.span
  have hoff (n : Nat) (hn : n≤128) : (row+UInt256.ofNat n).toNat = row.toNat+n :=
    uadd_word_ofNat_toNat _ _ (by omega)
  dsimp only [delegatedRevocationSetRevoker,delegatedRevocationLinkSignatures]
  rw [hoff 64 (by decide),hoff 96 (by decide)]
  let m1 := Reasoning.Theory.writeWord mem (row.toNat+64) sig
  let m2 := Reasoning.Theory.writeWord m1 (row.toNat+96) (UInt256.ofNat r.revoker.val)
  have hdata1 := hd.data.write_below (row.toNat+64) sig (by omega) hh
  have hdata2 := hdata1.write_below (row.toNat+96) (UInt256.ofNat r.revoker.val) (by omega) hh
  have hsig1 := hs.write_below (row.toNat+64) sig (by omega) hh
  have hsig2 := hsig1.write_below (row.toNat+96) (UInt256.ofNat r.revoker.val) (by omega) hh
  have hpres1 (n : Nat) (hn : n≤32) : memLoad (row+UInt256.ofNat n) m1 = memLoad (row+UInt256.ofNat n) mem := by
    exact memLoad_write_below _ _ _ _ (by rw [hoff n (by omega)]; omega) (by rw [hoff n (by omega)]; omega)
  have hpres2 (n : Nat) (hn : n≤64) : memLoad (row+UInt256.ofNat n) m2 = memLoad (row+UInt256.ofNat n) m1 := by
    apply memLoad_write_below
    · rw [hoff n (by omega)]; omega
    · rw [hoff n (by omega),writeWord_sparse_size]; omega
  have hrow1 : memLoad row m1 = r.schema := by
    have he := hpres1 0 (by decide)
    rw [show row+UInt256.ofNat 0 = row from u256_add_zero row] at he
    exact he.trans hd.schema
  have hrow2 : memLoad row m2 = r.schema := by
    have he := hpres2 0 (by decide)
    rw [show row+UInt256.ofNat 0 = row from u256_add_zero row] at he
    exact he.trans hrow1
  have hsigptr : memLoad (row+UInt256.ofNat 64) m1 = sig := by
    apply mloadWordValue_of_readWithPadding
    · rw [hoff 64 (by decide),writeWord_sparse_size]; omega
    · rw [hoff 64 (by decide)]; exact writeWord_sparse_read_back _ _ _
  have hrevoker : memLoad (row+UInt256.ofNat 96) m2 = UInt256.ofNat r.revoker.val := by
    apply mloadWordValue_of_readWithPadding
    · rw [hoff 96 (by decide),writeWord_sparse_size]; omega
    · rw [hoff 96 (by decide)]; exact writeWord_sparse_read_back _ _ _
  refine ⟨⟨hlo,by rw [writeWord_sparse_size]; omega,by omega,hrow2,
    (hpres2 32 (by decide)).trans ((hpres1 32 (by decide)).trans hd.dataPointer),
    (hpres2 64 (by decide)).trans hsigptr,hrevoker,hdata2,hsig2⟩,?_,?_⟩
  · exact (memLoad_write_below _ _ _ _ (by change 96 ≤ row.toNat+96; omega)
      (by rw [writeWord_sparse_size]; change 96 ≤ _; omega)).trans
      ((memLoad_write_below _ _ _ _ (by change 96 ≤ row.toNat+64; omega) (by change 96 ≤ mem.size; omega)).trans hf)
  · exact (memoryPrefix_sparse_writeWord mem (row.toNat+64) row.toNat sig (Or.inl (by omega))).trans
      (memoryPrefix_sparse_writeWord m1 (row.toNat+96) row.toNat (UInt256.ofNat r.revoker.val) (Or.inl (by omega)))

end Benchmarks.EAS.EAS
