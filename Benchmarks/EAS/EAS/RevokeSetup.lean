import Benchmarks.EAS.EAS.AttestArraysSource
import Benchmarks.EAS.EAS.RevokeLoopLocals
import Benchmarks.EAS.EAS.RevokeLoopMemory
import Benchmarks.EAS.EAS.AttestArrayMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

structure RevokeSetupLocals (L : Store) (site : RevokeSite) (rs : List RevocationRequestRecord)
    (s : SchemaRecord) (heap : Nat) : Prop where
  data : L.get? "data" = some (.array (rs.map RevocationRequestRecord.tuple))
  length : L.get? "length" = some (.int (Int.ofNat rs.length))
  schema : L.get? "schema" = some (wordBytes32Value site.schema)
  schemaRecord : L.get? "schemaRecord" = some s.value
  revoker : L.get? "revoker" = some (.address site.revoker)
  available : L.get? "availableValue" = some (.int (Int.ofNat site.available.toNat))
  last : L.get? "last" = some (.bool site.last)
  heap : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))
  db : L.get? "_db" = none

theorem revokeArraysLocals_view {L : Store} {site : RevokeSite} {rs : List RevocationRequestRecord}
    {s : SchemaRecord} {heap : Nat} (h : RevokeSetupLocals L site rs s heap) (middle next : Nat) :
    RevokeLoopLocals (attestArraysLocals L rs.length middle next) site rs s
      (List.replicate rs.length defaultAttestationRecord) (List.replicate rs.length ⟨0⟩) 0 next := by
  have keep (name : Ident) (h1 : ("i" == name) = false) (h2 : ("values" == name) = false)
      (h3 : ("allocation$allocation" == name) = false) (h4 : ("allocation" == name) = false)
      (h5 : ("$EAS.freeMemory" == name) = false) (h6 : ("attestations" == name) = false) :=
    attestArraysLocals_get L rs.length middle next name h1 h2 h3 h4 h5 h6
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.data
  · exact (keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.length
  · exact (keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.schema
  · exact (keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.schemaRecord
  · exact (keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.revoker
  · exact (keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.available
  · exact (keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.last
  · simp (disch := decide) only [attestArraysLocals,attestArrayLocals,store_get_ne,allocateBlockLocals_get,store_get_self]
  · simp (disch := decide) only [attestArraysLocals,store_get_ne,store_get_self]
  · exact store_get_self _ _ _
  · simp (disch := decide) only [attestArraysLocals,allocateBlockLocals,unpackHeapLocals,store_get_ne,store_get_self]
  · exact (keep _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.db

structure RevokeSetupMemory (mem : ByteArray) (site : RevokeSite) (rs : List RevocationRequestRecord) (s : SchemaRecord) : Prop where
  requests : RevocationRequestArrayMemoryView mem site.data rs site.schemaPtr.toNat
  schemaView : SchemaMemoryView mem site.schemaPtr s
  schemaHigh : site.schemaPtr.toNat+128 ≤ site.records.toNat
  zero : memLoad (UInt256.ofNat 96) mem = ⟨0⟩

theorem revokeArraysMemory_init {mem calldata : ByteArray} {site : RevokeSite}
    {rs : List RevocationRequestRecord} {s : SchemaRecord}
    (h : RevokeSetupMemory mem site rs s) (hlen : rs.length = site.length)
    (hv : site.values = UInt256.ofNat (allocateNext site.records.toNat (32+352*rs.length)))
    (hh : site.records.toNat ≤ 2^64-1) (hl : rs.length ≤ 2^64-1)
    (hr : allocateNext site.records.toNat (32+352*rs.length) ≤ 2^64-1) :
    let next := allocateNext (allocateNext site.records.toNat (32+352*rs.length)) (32+32*rs.length)
    MemoryPrefix mem (attestArraysMemory mem calldata site.records rs.length) site.records.toNat ∧
      RevokeLoopMemory (attestArraysMemory mem calldata site.records rs.length) site rs s
        (defaultArrayPointers site.records rs.length) (List.replicate rs.length ⟨0⟩)
        (List.replicate rs.length defaultAttestationRecord) next := by
  dsimp only
  let middle := allocateNext site.records.toNat (32+352*rs.length)
  let next := allocateNext middle (32+32*rs.length)
  let records := defaultArrayMemory mem site.records rs.length
  let final := attestArraysMemory mem calldata site.records rs.length
  have hsh := h.schemaHigh
  have hslo := h.schemaView.low
  have hsc := h.schemaView.covered
  have hlo : 128 ≤ site.records.toNat := by omega
  have hm : middle = site.records.toNat+32+352*rs.length := allocateNext_recordArray hh hl
  have hn : next = middle+32+32*rs.length := allocateNext_wordArray hr hl
  have hmid : (UInt256.ofNat middle).toNat = middle := ulit_toNat' _ (by change middle < 2^256; omega)
  have hb : middle < UInt256.size := by change middle < 2^256; omega
  obtain ⟨hp1,hcover1,hfree1,hptrs⟩ := defaultArrayMemory_view mem site.records rs.length (by omega) hh hl
  obtain ⟨hp2,hcover2,hlen2,hfree2,hvalues⟩ := wordArrayAllocationMemory_view records calldata
    (UInt256.ofNat middle) rs.length (by rw [hmid,hm]; omega) (by rw [hmid]; exact hr) hl
  simp only [hmid] at hp2 hcover2 hfree2 hvalues
  have hp : MemoryPrefix mem final site.records.toNat := hp1.trans (hp2.mono (by rw [hm]; omega))
  refine ⟨hp,h.requests.preserve (hp.mono (by omega)) site.schemaPtr.val.isLt,
    h.schemaView.preserve hp hsh site.records.val.isLt,hsh,
    (hptrs.preserve hp2 hb).mono (by change middle ≤ next; rw [hn]; omega),?_,?_,?_,defaultArrayPointers_length _ _,?_,hlen,?_,hfree2⟩
  · rw [hv]; exact hvalues
  · rw [hv,hmid]; exact hcover2
  · rw [hv,hmid,defaultArrayPointers_length,hm]; omega
  · simp only [List.length_replicate,defaultArrayPointers_length]
  · have hg := defaultArrayMemory_regions mem site.records (UInt256.ofNat 128) (UInt256.ofNat middle) rs.length
      (by decide) hh hl hlo (by rw [hmid]) (by omega) h.zero
    have hg' := hg.toRevoke hlo (by change 128 ≤ middle; rw [hm]; omega)
    rw [hv]
    exact hg'.preserve hp2 hb (by change middle ≤ next; rw [hn]; omega)

end Benchmarks.EAS.EAS
