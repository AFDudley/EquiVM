import Benchmarks.EAS.EAS.CopyViews
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: an initialized memory array of ABI words below an allocation boundary.
structure WordArrayMemoryView (mem : ByteArray) (ptr : UInt256) (words : List UInt256) (limit : Nat) : Prop where
  low : 96 ≤ ptr.toNat
  span : ptr.toNat+32+32*words.length ≤ limit
  covered : ptr.toNat+32+32*words.length ≤ mem.size
  length : memLoad ptr mem = UInt256.ofNat words.length
  words : memoryWords mem (ptr.toNat+32) words.length = words

theorem WordArrayMemoryView.preserve {before after : ByteArray} {ptr : UInt256}
    {words : List UInt256} {limit : Nat} (h : WordArrayMemoryView before ptr words limit)
    (hp : MemoryPrefix before after limit) (hlimit : limit < UInt256.size) :
    WordArrayMemoryView after ptr words limit := by
  refine ⟨h.low, h.span, le_trans h.covered hp.size, ?_, ?_⟩
  · exact (memLoad_of_prefix hp ptr h.low (by have := h.span; omega) (by have := h.covered; omega)).trans h.length
  · exact (memoryWords_prefix hp (ptr.toNat+32) words.length (by have := h.low; omega)
      h.span h.covered (by have := h.span; omega)).trans h.words

end Benchmarks.EAS.EAS
