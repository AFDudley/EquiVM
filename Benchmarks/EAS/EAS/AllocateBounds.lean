import Benchmarks.EAS.EAS.BytesAllocation
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: bounded allocation arithmetic does not wrap the EVM word.
theorem allocateNext_small {heap size : Nat} (hh : heap ≤ 2^64-1) (hs : size < 2^138) :
    allocateNext heap size = heap+(size+31)/32*32 := by
  have hs' : size+31 < UInt256.size := by change size+31 < 2^256; omega
  have hh' : heap+(size+31)/32*32 < UInt256.size := by change heap+(size+31)/32*32 < 2^256; omega
  simp only [allocateNext,allocateRounded,Nat.mod_eq_of_lt hs',Nat.mod_eq_of_lt hh']

theorem allocateNext_128 {heap : Nat} (hh : heap ≤ 2^64-1) :
    allocateNext heap 128 = heap+128 := by
  rw [allocateNext_small hh (by decide)]

theorem allocateNext_bytes {heap len : Nat} (hh : heap ≤ 2^64-1) (hl : len ≤ 2^64-1) :
    allocateNext heap (bytesAllocation len) = heap+bytesAllocation len := by
  rw [allocateNext_small hh (by unfold bytesAllocation; omega)]
  unfold bytesAllocation
  omega

end Benchmarks.EAS.EAS
