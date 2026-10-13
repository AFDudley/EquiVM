import Benchmarks.EAS.EAS.DelegatedRevocationMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

structure DelegatedRevocationDataMemoryView (mem : ByteArray) (row data : UInt256)
    (schema : UInt256) (rs : List RevocationRequestRecord) (heap : Nat) : Prop where
  low : 96 ≤ row.toNat
  covered : row.toNat+64 ≤ mem.size
  separation : row.toNat+128 ≤ data.toNat
  schema : memLoad row mem = schema
  dataPointer : memLoad (row+UInt256.ofNat 32) mem = data
  data : CopyRevocationArrayMemory mem data rs rs.length heap

theorem DelegatedRevocationDataMemoryView.preserve {before after : ByteArray} {row data schema : UInt256}
    {rs : List RevocationRequestRecord} {heap next : Nat}
    (h : DelegatedRevocationDataMemoryView before row data schema rs heap)
    (hp : MemoryPrefix before after heap) (hn : heap ≤ next) (hb : next < UInt256.size) :
    DelegatedRevocationDataMemoryView after row data schema rs next := by
  have hc := h.covered
  have he := h.data.span
  have hs := h.separation
  have hl := h.low
  have ho : (row+UInt256.ofNat 32).toNat = row.toNat+32 := uadd_word_ofNat_toNat _ _ (by omega)
  exact ⟨hl,le_trans hc hp.size,hs,(memLoad_of_prefix hp _ hl (by omega) (by omega)).trans h.schema,
    (memLoad_of_prefix hp _ (by rw [ho]; omega) (by rw [ho]; omega) (by rw [ho]; omega)).trans h.dataPointer,
    h.data.preserve hp hn hb⟩

theorem delegatedRevocationDataMemory_link {mem : ByteArray} {row data schema : UInt256}
    {rs : List RevocationRequestRecord} {heap : Nat}
    (hlo : 96 ≤ row.toNat) (hs : row.toNat+128 ≤ data.toNat) (hh : heap < UInt256.size)
    (hrow : memLoad row mem = schema) (hcover : row.toNat+32 ≤ mem.size)
    (hd : CopyRevocationArrayMemory mem data rs rs.length heap) :
    DelegatedRevocationDataMemoryView (delegatedRevocationLinkData mem row data) row data schema rs heap := by
  have he := hd.span
  have ho : (row+UInt256.ofNat 32).toNat = row.toNat+32 := uadd_word_ofNat_toNat _ _ (by omega)
  simp only [delegatedRevocationLinkData,ho]
  refine ⟨hlo,by rw [writeWord_sparse_size]; omega,hs,?_,?_,hd.write_below _ _ (by omega) hh⟩
  · exact (memLoad_write_below _ _ _ _ (by omega) hcover).trans hrow
  · apply mloadWordValue_of_readWithPadding
    · rw [ho,writeWord_sparse_size]; omega
    · rw [ho]; exact writeWord_sparse_read_back _ _ _

theorem delegatedRevocationDataMemory_of_copy {mem copied : ByteArray} {row data schema : UInt256}
    {rs : List RevocationRequestRecord} {heap : Nat}
    (hlo : 96 ≤ row.toNat) (hs : row.toNat+128 ≤ data.toNat) (hh : heap < UInt256.size)
    (hp : MemoryPrefix (recordPadding (delegatedRevocationSchemaMemory mem row schema) data.toNat) copied data.toNat)
    (hd : CopyRevocationArrayMemory copied data rs rs.length heap) :
    DelegatedRevocationDataMemoryView (delegatedRevocationLinkData copied row data) row data schema rs heap := by
  have he := hd.span
  have hp0 := (recordPadding_prefix (delegatedRevocationSchemaMemory mem row schema) data.toNat).trans hp
  have hc : row.toNat+32 ≤ (delegatedRevocationSchemaMemory mem row schema).size := by
    rw [delegatedRevocationSchemaMemory,writeWord_sparse_size]; omega
  apply delegatedRevocationDataMemory_link hlo hs hh ?_ (le_trans hc hp0.size) hd
  exact (memLoad_of_prefix hp0 _ hlo (by omega) hc).trans (delegatedRevocationSchemaMemory_load mem row schema)

end Benchmarks.EAS.EAS
