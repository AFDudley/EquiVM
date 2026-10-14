import Benchmarks.CurveVault.StringArithmetic

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: the three parts of a single dynamic-string ABI result.
theorem stringReturnEncoding (bytes : ByteArray) :
    encodeReturnValue? .string (.bytes bytes) =
      some ((((UInt256.ofNat 32).toByteArray ++ (UInt256.ofNat bytes.size).toByteArray) ++ bytes) ++
        ByteArray.zeroes (ABI.paddedSize bytes.size - bytes.size)) := by
  simp only [encodeReturnValue?, encodeReturnValues?, encodeABIValues?, abiTupleHeadSize?,
    isDynamicABIType, encodeABIValuesFrom?, encodeABIValue?, bind, Option.bind,
    List.length_nil, Nat.add_zero, List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp only [ByteArray.data_append, Array.toList_append,
    ← byteArray_toList_eq, ABI.natBytes, ABI.padRightToWord, ABI.zeroBytes,
    word_toBytesBE_eq_toByteArray_toList]
  rw [show bytes.toList.length = bytes.size by rw [byteArray_toList_eq, Array.length_toList]; rfl]
  rw [show (ByteArray.zeroes (ABI.paddedSize bytes.size - bytes.size)).toList =
    List.replicate (ABI.paddedSize bytes.size - bytes.size) 0 from by
      rw [byteArray_toList_eq, byteArray_zeroes_toList]]
  simp only [List.append_assoc]
  rfl

theorem stringEmptyReturnEncoding :
    encodeReturnValue? .string (.bytes ByteArray.empty) =
      some ((UInt256.ofNat 32).toByteArray ++ (UInt256.ofNat 0).toByteArray) := by
  rw [stringReturnEncoding]
  change some (((UInt256.ofNat 32).toByteArray ++ (UInt256.ofNat 0).toByteArray) ++ ByteArray.empty ++
    ByteArray.zeroes 0) = _
  rw [zeroes_zero (n := 0) rfl, ByteArray.append_empty, ByteArray.append_empty]

end Benchmarks.CurveVault
