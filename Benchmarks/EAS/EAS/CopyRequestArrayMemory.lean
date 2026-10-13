import Benchmarks.EAS.EAS.PointerTableMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def AttestationCopyRegion (mem : ByteArray) (ptr : UInt256) (r : AttestationRequestRecord) (lower heap : Nat) : Prop :=
  ∃ dp, AttestationRequestMemoryView mem ptr dp r ∧ ptr.toNat+192 ≤ heap ∧
    dp.toNat+32+32*((r.data.size+31)/32) ≤ heap ∧ lower ≤ ptr.toNat ∧ lower ≤ dp.toNat

abbrev CopyRequestArrayMemory := PointerTablePrefix AttestationCopyRegion

theorem CopyRequestArrayMemory.requests {mem : ByteArray} {array : UInt256}
    {rs : List AttestationRequestRecord} {i heap : Nat} (h : CopyRequestArrayMemory mem array rs i heap)
    (j : Nat) (hj : j < i) : ∃ ptr dp,
    memLoad (UInt256.ofNat (array.toNat+32+32*j)) mem = ptr ∧
    AttestationRequestMemoryView mem ptr dp (rs[j]'(lt_of_lt_of_le hj h.progress)) ∧
    ptr.toNat+192 ≤ heap ∧ dp.toNat+32+32*(((rs[j]'(lt_of_lt_of_le hj h.progress)).data.size+31)/32) ≤ heap ∧
    array.toNat+32+32*rs.length ≤ ptr.toNat ∧ array.toNat+32+32*rs.length ≤ dp.toNat := by
  obtain ⟨ptr,hptr,dp,hv,he,hd,hlo,hdl⟩ := h.elements j hj
  exact ⟨ptr,dp,hptr,hv,he,hd,hlo,hdl⟩

theorem CopyRequestArrayMemory.preserve {mem after : ByteArray} {array : UInt256}
    {rs : List AttestationRequestRecord} {i heap next : Nat}
    (h : CopyRequestArrayMemory mem array rs i heap) (hp : MemoryPrefix mem after heap)
    (hn : heap ≤ next) (hb : next < UInt256.size) : CopyRequestArrayMemory after array rs i next := by
  apply PointerTablePrefix.preserve h hp hn hb
  intro ptr r hr
  obtain ⟨dp,hv,he,hd,hlo,hdl⟩ := hr
  exact ⟨dp,hv.preserve hp he hd (by omega),by omega,by omega,hlo,hdl⟩

theorem CopyRequestArrayMemory.set {mem : ByteArray} {array ptr dp : UInt256}
    {rs : List AttestationRequestRecord} {i heap : Nat}
    (h : CopyRequestArrayMemory mem array rs i heap) (hi : i < rs.length)
    (hv : AttestationRequestMemoryView mem ptr dp rs[i])
    (he : ptr.toNat+192 ≤ heap) (hd : dp.toNat+32+32*((rs[i].data.size+31)/32) ≤ heap)
    (hlo : array.toNat+32+32*rs.length ≤ ptr.toNat) (hdl : array.toNat+32+32*rs.length ≤ dp.toNat)
    (hb : heap < UInt256.size) :
    CopyRequestArrayMemory (Reasoning.Theory.writeWord mem (array.toNat+32+32*i) ptr) array rs (i+1) heap := by
  apply PointerTablePrefix.set h hi ⟨dp,hv,he,hd,hlo,hdl⟩ hb
  intro p r hr
  obtain ⟨d,hv',he',hd',hl',hdl'⟩ := hr
  exact ⟨d,hv'.write_below _ ptr (by omega) (by omega) (by omega),he',hd',hl',hdl'⟩

theorem CopyRequestArrayMemory.finish {mem : ByteArray} {array : UInt256}
    {rs : List AttestationRequestRecord} {heap lower : Nat}
    (h : CopyRequestArrayMemory mem array rs rs.length heap) (hl : lower ≤ array.toNat) :
    AttestationRequestArrayRegion mem array rs lower heap := by
  refine ⟨⟨h.low,h.span,h.covered,h.length,?_⟩,hl,?_⟩
  · intro j hj
    obtain ⟨ptr,dp,hp,hv,he,hd,_,_⟩ := h.requests j hj
    exact ⟨ptr,dp,hp,hv,he,hd⟩
  · intro j hj
    obtain ⟨ptr,dp,hp,hv,he,hd,hlo,hdl⟩ := h.requests j hj
    rw [hp,hv.pointer]
    constructor <;> omega

theorem copyRequestArrayMemory_init (mem : ByteArray) (array : UInt256) (rs : List AttestationRequestRecord)
    (hlo : 96 ≤ array.toNat) (hh : array.toNat ≤ 2^64-1) (hlen : rs.length ≤ 2^64-1) :
    let next := allocateNext array.toNat (32+32*rs.length)
    let final := arrayAllocationHeaderMemory mem array rs.length
    MemoryPrefix mem final array.toNat ∧ CopyRequestArrayMemory final array rs 0 next ∧
    memLoad (UInt256.ofNat 64) final = UInt256.ofNat next := by
  exact pointerTablePrefix_init AttestationCopyRegion mem array rs hlo hh hlen

end Benchmarks.EAS.EAS
