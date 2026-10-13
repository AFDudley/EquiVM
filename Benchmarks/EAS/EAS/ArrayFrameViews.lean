import Benchmarks.EAS.EAS.RecordArrayMemory
import Benchmarks.EAS.EAS.WordArrayMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- GENERALIZES readWithPadding_prefix to an arbitrary initialized subwindow.
theorem readWithPadding_window (mem : ByteArray) (off full start len : Nat)
    (hpart : start+len ≤ full) (hin : off+full ≤ mem.size) :
    (mem.readWithPadding off full).extract start (start+len) = mem.readWithPadding (off+start) len := by
  by_cases hz : len=0
  · rw [hz, Nat.add_zero, byteArray_readWithPadding_zero]
    exact byteArray_extract_empty_of_le _ (le_refl _)
  rw [readWithPadding_eq_extract_unbounded mem off full (by omega) hin, extract_extract_BA,
    readWithPadding_eq_extract_unbounded mem (off+start) len (by omega) (by omega)]
  rw [Nat.min_eq_left (by omega : off+(start+len) ≤ off+full)]
  congr 1
  omega

-- LIBRARY CANDIDATE: a short read ending inside a preserved word is preserved.
theorem memoryPrefix_read_suffix {before after : ByteArray} {limit : Nat}
    (hp : MemoryPrefix before after limit) (off len : Nat)
    (hlen : len ≤ 32) (hlo : 128 ≤ off+len) (hhi : off+len ≤ limit) (hin : off+len ≤ before.size) :
    after.readWithPadding off len = before.readWithPadding off len := by
  have hend : off+len-32+32=off+len := by omega
  have hstart : off+len-32+(32-len)=off := by omega
  have hb := readWithPadding_window before (off+len-32) 32 (32-len) len (by omega) (by omega)
  have ha := readWithPadding_window after (off+len-32) 32 (32-len) len (by omega) (by have := hp.size; omega)
  rw [hstart] at ha hb
  rw [← ha, ← hb, hp.read _ (by omega) (by omega) (by omega)]

theorem WordArrayMemoryView.mono {mem : ByteArray} {ptr : UInt256} {words : List UInt256} {limit limit' : Nat}
    (h : WordArrayMemoryView mem ptr words limit) (hle : limit ≤ limit') :
    WordArrayMemoryView mem ptr words limit' :=
  ⟨h.low, le_trans h.span hle, h.covered, h.length, h.words⟩

theorem AttestationArrayMemoryView.mono {mem : ByteArray} {ptr : UInt256} {ats : List AttestationRecord} {limit limit' : Nat}
    (h : AttestationArrayMemoryView mem ptr ats limit) (hle : limit ≤ limit') :
    AttestationArrayMemoryView mem ptr ats limit' := by
  refine ⟨h.low, le_trans h.span hle, h.covered, h.length, ?_⟩
  intro i hi
  obtain ⟨src,dp,hs,hv,hsrc,hdata⟩ := h.records i hi
  exact ⟨src,dp,hs,hv,le_trans hsrc hle,le_trans hdata hle⟩

end Benchmarks.EAS.EAS
