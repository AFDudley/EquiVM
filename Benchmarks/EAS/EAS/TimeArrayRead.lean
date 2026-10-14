import Benchmarks.EAS.EAS.TimeArray
import Benchmarks.EAS.EAS.TimeArrayEVM
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: a materialized calldata word list has the same indexed reads as the EVM array.
theorem calldataWordList_read {cd : ByteArray} {ee : ExecutionEnv} {start count : Nat}
    (hcd : ee.calldata = cd) (hbound : start + 32 * count ≤ cd.size) (hsize : cd.size < UInt256.size) :
    ∀ i, i < (calldataWordList cd start count).length →
      lookupNth? (calldataWordList cd start count) i =
        some (timeArrayWord ee (UInt256.ofNat start) (UInt256.ofNat i)) := by
  intro i hi
  have hi' : i < count := by simpa only [calldataWordList, List.length_map, List.length_range] using hi
  have hprod : 32 * i < UInt256.size := by omega
  have hstart : start < UInt256.size := by omega
  have haddr : (UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) + UInt256.ofNat start).toNat = start + 32 * i := by
    change (UInt256.shiftLeft (UInt256.ofNat i) ⟨5⟩ + UInt256.ofNat start).toNat = _
    rw [shiftLeft5_ofNat_eq hprod]
    change (UInt256.add (UInt256.ofNat (32 * i)) (UInt256.ofNat start)).toNat = _
    rw [uadd_ofNat_toNat hprod hstart (by omega)]
    omega
  simp only [timeArrayWord, hcd, haddr, calldataWordList, lookupNth_getElem, List.getElem?_map,
    List.getElem?_range hi', Option.map_some]

end Benchmarks.EAS.EAS
