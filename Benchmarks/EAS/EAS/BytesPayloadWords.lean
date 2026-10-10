import Benchmarks.EAS.EAS.BytesWordMask
import Benchmarks.EAS.EAS.ArrayFrameViews
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: full word loads inside an initialized dynamic payload.
theorem payloadMemoryWord {mem bytes : ByteArray} {off idx : Nat}
    (hread : mem.readWithPadding off bytes.size = bytes) (hin : off+bytes.size ≤ mem.size)
    (hpart : idx+32 ≤ bytes.size) (hb : off+idx < UInt256.size) :
    memLoad (UInt256.ofNat (off+idx)) mem = uInt256OfByteArray (bytes.readWithPadding idx 32) := by
  have hr : mem.readWithPadding (off+idx) 32 = bytes.readWithPadding idx 32 := by
    rw [← readWithPadding_window mem off bytes.size idx 32 hpart hin,hread,
      readWithPadding_eq_extract_unbounded bytes idx 32 (by decide) hpart]
  have hw := memLoad_bytes mem (off+idx) hb (by omega)
  rw [hr] at hw
  exact (uInt256OfByteArray_toByteArray _).symm.trans (congrArg uInt256OfByteArray hw)

-- LIBRARY CANDIDATE: the final partial payload word is its memory prefix, padded with zeros.
theorem payloadMemoryTail {mem bytes : ByteArray} {off idx : Nat}
    (hread : mem.readWithPadding off bytes.size = bytes) (hin : off+idx+32 ≤ mem.size)
    (hpart : idx < bytes.size) (htail : bytes.size-idx < 32) (hb : off+idx < UInt256.size) :
    UInt256.land (UInt256.ofNat (2^256-2^(8*(32-(bytes.size-idx)))))
      (memLoad (UInt256.ofNat (off+idx)) mem) = uInt256OfByteArray (bytes.readWithPadding idx 32) := by
  rw [wordPrefixMask _ _ htail,memLoad_bytes mem (off+idx) hb hin,
    readWithPadding_prefix mem (off+idx) 32 (bytes.size-idx) (by omega) hin,
    ← readWithPadding_window mem off bytes.size idx (bytes.size-idx) (by omega) (by omega),hread]
  congr 1
  have he : idx+(bytes.size-idx) = bytes.size := by omega
  rw [he]
  unfold ByteArray.readWithPadding ByteArray.readWithoutPadding
  rw [if_neg (by omega : ¬idx ≥ bytes.size)]
  have hex : bytes.extract idx (idx+min 32 bytes.size) = bytes.extract idx bytes.size := by
    apply ByteArray.ext
    simp only [ByteArray.data_extract]
    apply Array.extract_eq_extract_right.mpr
    change min (idx+min 32 bytes.size-idx) (bytes.size-idx) = min (bytes.size-idx) (bytes.size-idx)
    omega
  rw [hex]
  have hsize : (bytes.extract idx bytes.size).size = bytes.size-idx := by rw [ByteArray.size_extract]; omega
  rw [if_neg (by rw [hsize]; omega)]
  rw [Nat.min_eq_right (by rw [hsize]; omega)]
  simp only [Nat.zero_add,byteArray_extract_self]

end Benchmarks.EAS.EAS
