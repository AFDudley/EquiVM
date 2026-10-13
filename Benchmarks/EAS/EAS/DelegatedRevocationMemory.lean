import Benchmarks.EAS.EAS.DelegatedRevocationDecode
import Benchmarks.EAS.EAS.PointerTableLowWrite
import Benchmarks.EAS.EAS.DelegatedRevocationSignatureAccess
import Benchmarks.EAS.EAS.DelegatedRevocationAccess
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

structure DelegatedRevocationBatchMemoryView (mem : ByteArray) (row data sig : UInt256)
    (r : DelegatedRevocationBatch) (heap : Nat) : Prop where
  low : 96 ≤ row.toNat
  covered : row.toNat+128 ≤ mem.size
  span : row.toNat+128 ≤ heap
  schema : memLoad row mem = r.schema
  dataPointer : memLoad (row+UInt256.ofNat 32) mem = data
  sigPointer : memLoad (row+UInt256.ofNat 64) mem = sig
  revoker : memLoad (row+UInt256.ofNat 96) mem = UInt256.ofNat r.revoker.val
  data : CopyRevocationArrayMemory mem data r.data r.data.length heap
  signatures : CopySignatureArrayMemory mem sig r.signatures r.signatures.length heap

theorem DelegatedRevocationBatchMemoryView.preserve {before after : ByteArray} {row data sig : UInt256}
    {r : DelegatedRevocationBatch} {heap next : Nat} (h : DelegatedRevocationBatchMemoryView before row data sig r heap)
    (hp : MemoryPrefix before after heap) (hn : heap ≤ next) (hb : next < UInt256.size) :
    DelegatedRevocationBatchMemoryView after row data sig r next := by
  have hc := h.covered
  have hs := h.span
  have hl := h.low
  have hfield (n : Nat) (hn' : n≤96) : memLoad (row+UInt256.ofNat n) after = memLoad (row+UInt256.ofNat n) before := by
    have ho : (row+UInt256.ofNat n).toNat = row.toNat+n := uadd_word_ofNat_toNat _ _ (by omega)
    exact memLoad_of_prefix hp _ (by rw [ho]; omega) (by rw [ho]; omega) (by rw [ho]; omega)
  exact ⟨hl,le_trans hc hp.size,le_trans hs hn,
    (memLoad_of_prefix hp _ hl (by omega) (by omega)).trans h.schema,
    (hfield 32 (by decide)).trans h.dataPointer,(hfield 64 (by decide)).trans h.sigPointer,
    (hfield 96 (by decide)).trans h.revoker,h.data.preserve hp hn hb,h.signatures.preserve hp hn hb⟩

def delegatedRevocationSetRevoker (mem : ByteArray) (row word : UInt256) : ByteArray :=
  Reasoning.Theory.writeWord mem (row+UInt256.ofNat 96).toNat word

theorem delegatedRevocationReservedMemory_free (mem : ByteArray) (row : UInt256) :
    memLoad (UInt256.ofNat 64) (delegatedRevocationReservedMemory mem row) = UInt256.ofNat (row.toNat+128) := by
  apply mloadWordValue_of_readWithPadding
  · rw [delegatedRevocationReservedMemory,writeWord_sparse_size]; change 64 < _; omega
  · exact writeWord_sparse_read_back _ _ _

theorem delegatedRevocationSchemaMemory_free (mem : ByteArray) (row schema : UInt256) (hl : 96 ≤ row.toNat) :
    memLoad (UInt256.ofNat 64) (delegatedRevocationSchemaMemory (delegatedRevocationReservedMemory mem row) row schema) =
      UInt256.ofNat (row.toNat+128) := by
  exact (memLoad_write_below _ _ _ _ hl
    (by rw [delegatedRevocationReservedMemory,writeWord_sparse_size]; change 96 ≤ _; omega)).trans
      (delegatedRevocationReservedMemory_free mem row)

theorem delegatedRevocationSchemaMemory_load (mem : ByteArray) (row schema : UInt256) :
    memLoad row (delegatedRevocationSchemaMemory mem row schema) = schema := by
  apply mloadWordValue_of_readWithPadding
  · rw [delegatedRevocationSchemaMemory,writeWord_sparse_size]; omega
  · exact writeWord_sparse_read_back _ _ _

end Benchmarks.EAS.EAS
