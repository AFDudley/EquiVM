import Benchmarks.EAS.EAS.PackedShift
import Benchmarks.EAS.EAS.ByteViews
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

-- GENERALIZES Reasoning.Memory.tailMask_toByteArray to a numeric mask, including an empty prefix.
theorem wordPrefixMask (word : UInt256) (len : Nat) (hlen : len < 32) :
    UInt256.land (UInt256.ofNat (2^256-2^(8*(32-len)))) word =
      uInt256OfByteArray ((word.toByteArray.extract 0 len).readWithPadding 0 32) := by
  by_cases hz : len = 0
  · subst len
    change UInt256.land ⟨0⟩ word = _
    rw [u256_land_zero_left,byteArray_extract_empty_of_le _ (le_refl _),empty_readWithPadding_word_zero]
  have hsize : (word.toByteArray.extract 0 len).size = len := by
    rw [ByteArray.size_extract,toByteArray_size]
    omega
  have hr := readWithPadding_zero_toList_of_size_lt32 (word.toByteArray.extract 0 len)
    (by rw [hsize]; exact hz) (by rw [hsize]; exact hlen)
  rw [hsize] at hr
  have hn : fromByteArrayBigEndian ((word.toByteArray.extract 0 len).readWithPadding 0 32) =
      word.toNat / 2^(8*(32-len))*2^(8*(32-len)) := by
    change fromBytesBigEndian (((word.toByteArray.extract 0 len).readWithPadding 0 32).toList) = _
    rw [hr,fromBytesBigEndian_append_zeros,bytesBE_extract_high word len (by omega)]
  rw [uInt256OfByteArray_eq,hn,← u256_land_high_mask_toNat word (8*(32-len)) (by omega),u256_ofNat_toNat]

end Benchmarks.EAS.EAS
