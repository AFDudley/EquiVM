import Benchmarks.EAS.EAS.CalldataRead
import Benchmarks.EAS.EAS.ReturnDecode
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: a partial calldata word is its available slice followed by zero padding.
theorem calldataWord_paddedSlice (cd : ByteArray) (offset : UInt256) :
    (cd.extract offset.toNat (offset.toNat+min (cd.size-offset.toNat) 32)).toList ++
      (ByteArray.mk (Array.replicate (32-min (cd.size-offset.toNat) 32) (0 : UInt8))).toList =
      EVM.Word.toBytesBE (calldataWord cd offset.toNat) := by
  rw [← solcReadBytes_word_total,extract_toList,Nat.add_sub_cancel_left]
  rw [ABI.Solc08Calldata.solcReadBytes,
    Nat.mod_eq_of_lt (show offset.toNat<EVM.wordModulus from offset.val.isLt)]
  simp only [byteArray_toList_eq,Array.toList_replicate]
  have hl : (cd.data.toList.drop offset.toNat).length=cd.size-offset.toNat := by
    simp only [List.length_drop,Array.length_toList,ByteArray.size]
  have ht : (cd.data.toList.drop offset.toNat).take (min (cd.size-offset.toNat) 32)=
      (cd.data.toList.drop offset.toNat).take 32 := by
    rw [← hl,Nat.min_comm,← List.take_take,List.take_length]
  rw [ht,List.length_take,hl,Nat.min_comm]


theorem decodeReturnUint_wordBytes {out : ByteArray} (word : UInt256)
    (he : out.toList=EVM.Word.toBytesBE word) :
    config.externalABI.decodeValue? abiUInt256 out=some (.int (Int.ofNat word.toNat)) := by
  have hs : out.size=32 := by have ht := congrArg List.length he; simpa only [byteArray_toList_eq,Array.length_toList,word_toBytesBE_length_32] using ht
  change ABI.decodeReturnValueWithMode? (.solc08Calldata easPlanTable) abiUInt256 out=_
  rw [decodeReturnSolc08Scalar_eq easPlanTable _ out rfl (by omega)]
  rw [decodeReturnUint_long (by omega) (by omega)]
  have hw := decode_word_at_eq_any out 0 (by omega)
  change bytesToWord ((out.toList.drop 0).take 32)=calldataWord out 0 at hw
  rw [List.drop_zero,he,List.take_of_length_le (by rw [word_toBytesBE_length_32]),bytesToWord_toBytesBE] at hw
  rw [← hw]

end Benchmarks.EAS.EAS
