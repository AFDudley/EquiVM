import Benchmarks.EAS.EAS.WordArrayMemory
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: reflect an array view through a preserved prefix when its bytes were already covered.
theorem WordArrayMemoryView.reflect {before after : ByteArray} {ptr : UInt256}
    {words : List UInt256} {limit : Nat} (h : WordArrayMemoryView after ptr words limit)
    (hp : MemoryPrefix before after limit) (hin : ptr.toNat+32+32*words.length ≤ before.size)
    (hb : limit < UInt256.size) : WordArrayMemoryView before ptr words limit := by
  refine ⟨h.low,h.span,hin,?_,?_⟩
  · exact (memLoad_of_prefix hp ptr h.low (by have := h.span; omega) (by omega)).symm.trans h.length
  · exact (memoryWords_prefix hp (ptr.toNat+32) words.length (by have := h.low; omega)
      h.span hin (by have := h.span; omega)).symm.trans h.words

end Benchmarks.EAS.EAS
