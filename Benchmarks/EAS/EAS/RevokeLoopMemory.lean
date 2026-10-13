import Benchmarks.EAS.EAS.RevokeUpdateMemory
import Benchmarks.EAS.EAS.SchemaMemory
import Benchmarks.EAS.EAS.WordArrayReflect
import Benchmarks.EAS.EAS.PaddingLowWrite
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

structure RevokeLoopMemory (mem : ByteArray) (site : RevokeSite) (rs : List RevocationRequestRecord)
    (s : SchemaRecord) (ptrs values : List UInt256) (ats : List AttestationRecord) (heap : Nat) : Prop where
  requests : RevocationRequestArrayMemoryView mem site.data rs site.schemaPtr.toNat
  schemaView : SchemaMemoryView mem site.schemaPtr s
  schemaHigh : site.schemaPtr.toNat+128 ≤ site.records.toNat
  records : WordArrayMemoryView mem site.records ptrs heap
  valueArray : WordArrayMemoryView (recordPadding mem heap) site.values values heap
  valueCovered : site.values.toNat+32 ≤ mem.size
  recordValues : site.records.toNat+32+32*ptrs.length ≤ site.values.toNat
  lengthRequests : ptrs.length = rs.length
  lengthValues : values.length = ptrs.length
  lengthSite : rs.length = site.length
  regions : RevokeRecordRegions mem site.records site.values ptrs ats heap
  heapRead : memLoad (UInt256.ofNat 64) mem = UInt256.ofNat heap

theorem RevokeLoopMemory.valueLength {mem : ByteArray} {site : RevokeSite} {rs : List RevocationRequestRecord}
    {s : SchemaRecord} {ptrs values : List UInt256} {ats : List AttestationRecord} {heap : Nat}
    (h : RevokeLoopMemory mem site rs s ptrs values ats heap) :
    memLoad site.values mem = UInt256.ofNat values.length := by
  have he := memLoad_of_prefix (recordPadding_prefix mem heap) site.values h.valueArray.low
    (by have := h.valueArray.span; omega) h.valueCovered
  exact he.symm.trans h.valueArray.length

theorem RevokeLoopMemory.next {before mid : ByteArray} {site : RevokeSite} {src dp value word : UInt256}
    {rs : List RevocationRequestRecord} {s : SchemaRecord} {ptrs values : List UInt256}
    {ats : List AttestationRecord} {a : AttestationRecord} {next i : Nat}
    (h : RevokeLoopMemory before site rs s ptrs values ats src.toNat)
    (hcore : MemoryPrefix before mid src.toNat)
    (hpad : MemoryPrefix (recordPadding before src.toNat) mid src.toNat)
    (hv : AttestationMemoryView mid src dp a) (hi : i < ptrs.length) (hb : next < UInt256.size)
    (hn : src.toNat+320 ≤ next) (hd : dp.toNat+32+32*((a.data.size+31)/32) ≤ next)
    (hdlo : src.toNat ≤ dp.toNat) (hh : memLoad (UInt256.ofNat 64) mid = UInt256.ofNat next) :
    RevokeLoopMemory (revokeUpdateMemory mid site src (UInt256.ofNat next) value word i)
      site rs s (ptrs.set i src) (values.set i value) (ats.set i a) next := by
  have hvlen := h.lengthValues
  have has := h.records.span
  have hvs := h.valueArray.span
  have hav := h.recordValues
  have hsch := h.schemaHigh
  have ha := (h.records.preserve hcore src.val.isLt).mono (by omega : src.toNat ≤ next)
  have hval := (h.valueArray.preserve hpad src.val.isLt).mono (by omega : src.toNat ≤ next)
  obtain ⟨ha',hv',hh'⟩ := revokeUpdateMemory_views site ha hval hav hi (by omega) hb
  have hp := revokeUpdateMemory_prefix mid site src (UInt256.ofNat next) value word i
    (by omega) (by rw [ulit_toNat' next hb]; omega)
  have hf := (hcore.mono (by omega : site.records.toNat ≤ src.toNat)).trans hp
  have hr := h.regions.preserve hcore src.val.isLt (by omega : src.toNat ≤ next)
  refine ⟨h.requests.preserve (hf.mono (by omega)) site.schemaPtr.val.isLt,
    h.schemaView.preserve hf hsch site.records.val.isLt,hsch,ha',
    hv'.preserve (recordPadding_prefix _ next) hb,(by have := hv'.covered; omega),?_,?_,?_,h.lengthSite,?_,hh'.trans hh⟩
  · simpa only [List.length_set] using hav
  · simpa only [List.length_set] using h.lengthRequests
  · simpa only [List.length_set] using hvlen
  · exact hr.update site hv hi hb hav hn (by omega) hd hdlo

end Benchmarks.EAS.EAS
