import Benchmarks.EAS.EAS.ReturnWordDecode
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS

-- GENERALIZES Reasoning.Theory.readBytes32_toList to arbitrary addresses and lengths.
theorem readBytes_padded_toList (cd : ByteArray) (start size : Nat) :
    (cd.readBytes start size).toList =
      (cd.toList.drop start).take size ++ List.replicate (size-((cd.toList.drop start).take size).length) 0 := by
  unfold ByteArray.readBytes
  split
  · have hcopy : (cd.copySlice start ByteArray.empty 0 size).toList = (cd.toList.drop start).take size := by
      have h : (cd.copySlice start ByteArray.empty 0 size).data = cd.data.extract start (start+size) := by
        rw [ByteArray.data_copySlice]; simp
      rw [byteArray_toList_eq,h,Array.toList_extract,List.extract_eq_take_drop,Nat.add_sub_cancel_left,byteArray_toList_eq]
    have hsize : (cd.copySlice start ByteArray.empty 0 size).size = ((cd.toList.drop start).take size).length := by
      rw [← hcopy,byteArray_toList_eq,Array.length_toList]; rfl
    rw [byteArray_toList_eq (_ ++ _),ByteArray.data_append,Array.toList_append,← byteArray_toList_eq,hcopy,
      byteArray_zeroes_toList,hsize]
  · simp only [byteArray_toList_eq,ByteArray.data_append,Array.toList_append,List.toList_toArray,
      ByteArray.size,List.size_toArray,byteArray_zeroes_toList]

-- GENERALIZES solcReadBytes_word: include partial and out-of-bounds CALLDATALOADs.
theorem solcReadBytes_word_total (cd : ByteArray) (start : UInt256) :
    solcReadBytes cd.toList start.toNat 32 = EVM.Word.toBytesBE (calldataWord cd start.toNat) := by
  have he : solcReadBytes cd.toList start.toNat 32 = (cd.readBytes start.toNat 32).toList := by
    rw [readBytes_padded_toList]
    simp only [solcReadBytes,Nat.mod_eq_of_lt (show start.toNat < EVM.wordModulus from start.val.isLt)]
  have hl : (solcReadBytes cd.toList start.toNat 32).length = 32 := by
    simp only [solcReadBytes,List.length_append,List.length_replicate,List.length_take,List.length_drop]
    omega
  have hword : bytesToWord (solcReadBytes cd.toList start.toNat 32) = calldataWord cd start.toNat := by
    rw [he]
    change _ = uInt256OfByteArray _
    rw [uInt256OfByteArray_eq]
    unfold bytesToWord fromByteArrayBigEndian
    congr 2
    simp only [byteArray_toList_eq,List.toList_toArray]
  exact (hword ▸ toBytesBE_bytesToWord_of_length hl).symm

-- GENERALIZES solcReadNat_word to every EVM word address.
theorem solcReadNat_word_total (cd : ByteArray) (start : UInt256) :
    solcReadNat cd.toList start.toNat = (calldataWord cd start.toNat).toNat := by
  rw [solcReadNat,solcReadBytes_word_total,bytesToWord_toBytesBE]

-- GENERALIZES decodeSolcScalar to arbitrary plans, pointer policies and padded words.
theorem decodeSolcScalar_total (out : ByteArray) (start : UInt256) (elem : ElemType)
    (plan : CalldataPlan) (tailAccess : Bool) (hscalar : isABIScalarWordType (.elem elem) = true) :
    decodeValue? (.elem elem) out.toList start.toNat plan tailAccess =
      decodeABIWord? (.elem elem) (calldataWord out start.toNat) := by
  have ht : List.take 32 (EVM.Word.toBytesBE (calldataWord out start.toNat)) = EVM.Word.toBytesBE (calldataWord out start.toNat) :=
    List.take_of_length_le (by rw [word_toBytesBE_length_32])
  rw [decodeValue?,solcReadBytes_word_total,decodeABIValue_scalarWord_eq hscalar]
  simp only [decodeScalarWord?,readWord?,readBytes?,List.drop_zero,ht,word_toBytesBE_length_32,
    if_true,bind,Option.bind,bytesToWord_toBytesBE]
  cases decodeABIWord? (.elem elem) (calldataWord out start.toNat) <;> rfl

end Benchmarks.EAS.EAS
