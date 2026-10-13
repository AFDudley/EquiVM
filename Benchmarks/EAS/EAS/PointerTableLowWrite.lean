import Benchmarks.EAS.EAS.RevocationCopyMemory
import Benchmarks.EAS.EAS.SignatureArrayMemory
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: writes before a pointer table preserve its entries and bounded records.
theorem PointerTablePrefix.write_below {α : Type} {view : ByteArray → UInt256 → α → Nat → Nat → Prop}
    {mem : ByteArray} {array : UInt256} {rs : List α} {i heap : Nat}
    (h : PointerTablePrefix view mem array rs i heap) (dst : Nat) (word : UInt256)
    (hs : dst+32 ≤ array.toNat) (hb : heap < UInt256.size)
    (hv : ∀ ptr r, view mem ptr r (array.toNat+32+32*rs.length) heap →
      view (Reasoning.Theory.writeWord mem dst word) ptr r (array.toNat+32+32*rs.length) heap) :
    PointerTablePrefix view (Reasoning.Theory.writeWord mem dst word) array rs i heap := by
  have he := h.span
  have hc := h.covered
  have hi := h.progress
  refine ⟨h.low,h.progress,h.span,by rw [writeWord_sparse_size]; omega,?_,?_⟩
  · exact (memLoad_write_above _ _ _ _ hs (by omega)).trans h.length
  · intro j hj
    obtain ⟨ptr,hp,hr⟩ := h.elements j hj
    have hslot : (UInt256.ofNat (array.toNat+32+32*j)).toNat = array.toNat+32+32*j := ulit_toNat' _ (by omega)
    exact ⟨ptr,(memLoad_write_above _ _ _ _ (by rw [hslot]; omega) (by rw [hslot]; omega)).trans hp,hv ptr rs[j] hr⟩

theorem CopyRevocationArrayMemory.write_below {mem : ByteArray} {array : UInt256}
    {rs : List RevocationRequestRecord} {i heap : Nat} (h : CopyRevocationArrayMemory mem array rs i heap)
    (dst : Nat) (word : UInt256) (hs : dst+32 ≤ array.toNat) (hb : heap < UInt256.size) :
    CopyRevocationArrayMemory (Reasoning.Theory.writeWord mem dst word) array rs i heap := by
  apply PointerTablePrefix.write_below h dst word hs hb
  intro ptr r hr
  exact ⟨hr.1.write_below dst word (by have := hr.2.1; omega) (by have := hr.2.2; omega),hr.2⟩

theorem CopySignatureArrayMemory.write_below {mem : ByteArray} {array : UInt256}
    {ss : List SignatureRecord} {i heap : Nat} (h : CopySignatureArrayMemory mem array ss i heap)
    (dst : Nat) (word : UInt256) (hs : dst+32 ≤ array.toNat) (hb : heap < UInt256.size) :
    CopySignatureArrayMemory (Reasoning.Theory.writeWord mem dst word) array ss i heap := by
  apply PointerTablePrefix.write_below h dst word hs hb
  intro ptr r hr
  exact ⟨hr.1.write_below dst word (by have := hr.2.1; omega) (by have := hr.2.2; omega),hr.2⟩

theorem CopyRevocationArrayMemory.preserve {before after : ByteArray} {array : UInt256}
    {rs : List RevocationRequestRecord} {i heap next : Nat} (h : CopyRevocationArrayMemory before array rs i heap)
    (hp : MemoryPrefix before after heap) (hn : heap ≤ next) (hb : next < UInt256.size) :
    CopyRevocationArrayMemory after array rs i next := by
  apply PointerTablePrefix.preserve h hp hn hb
  intro ptr r hr
  exact ⟨hr.1.preserve hp hr.2.1 (by omega),le_trans hr.2.1 hn,hr.2.2⟩

theorem CopySignatureArrayMemory.preserve {before after : ByteArray} {array : UInt256}
    {ss : List SignatureRecord} {i heap next : Nat} (h : CopySignatureArrayMemory before array ss i heap)
    (hp : MemoryPrefix before after heap) (hn : heap ≤ next) (hb : next < UInt256.size) :
    CopySignatureArrayMemory after array ss i next := by
  apply PointerTablePrefix.preserve h hp hn hb
  intro ptr r hr
  exact ⟨hr.1.preserve hp hr.2.1 (by omega),le_trans hr.2.1 hn,hr.2.2⟩

end Benchmarks.EAS.EAS
