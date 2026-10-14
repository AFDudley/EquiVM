import Benchmarks.Morpho.MetaMorphoV1_1.SafeTransferABI
import Benchmarks.Morpho.MetaMorphoV1_1.EncodedWordCallMemory
import Benchmarks.Morpho.MetaMorphoV1_1.BytesBuffer

/-! Approval call encoding and the corresponding allocated request buffer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def constructorApproveSelector : ByteArray := ⟨#[0x09, 0x5e, 0xa7, 0xb3]⟩
def constructorApproveSelectorWord : UInt256 := UInt256.shiftLeft ⟨157198259⟩ ⟨224⟩
def constructorApproveCalldata (spender : AccountAddress) (value : UInt256) : ByteArray :=
  constructorApproveSelector ++ ((UInt256.ofNat spender.val).toByteArray ++ value.toByteArray)

theorem constructorApproveCalldata_size (spender : AccountAddress) (value : UInt256) :
    (constructorApproveCalldata spender value).size = 68 := by
  simp only [constructorApproveCalldata, ByteArray.size_append, toByteArray_size]
  rfl

theorem constructorApproveEncode (spender : AccountAddress) (value : UInt256) :
    config.externalABI.encode? "approve" [.address spender, uint256Value value] =
      some (constructorApproveCalldata spender value) := by
  change encodeCallWithSelector?
    (ByteArray.mk ((EVM.Word.ofNat 0x095ea7b3).toBytesBE.drop 28).toArray)
    [abiAddress, abiUInt256] [.address spender, uint256Value value] = _
  rw [show ByteArray.mk ((EVM.Word.ofNat 0x095ea7b3).toBytesBE.drop 28).toArray =
    constructorApproveSelector from by decide +kernel]
  have hh : abiTupleHeadSize? [abiAddress, abiUInt256] = some 64 := by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, abiAddress, abiUInt256]
  rw [encodeCallWithSelector?, encodeABIValues?, hh]
  simp only [encodeABIValuesFrom?, encodeAddressWord, encodeABIValue_uint256_word,
    show isDynamicABIType abiAddress = false from rfl,
    show isDynamicABIType abiUInt256 = false from rfl,
    bind, Option.bind, Bool.false_eq_true, if_false, List.nil_append, List.append_nil,
    List.toByteArray_append, byteArray_toList_toByteArray]
  rfl

def constructorApproveMemory (mem : ByteArray) (ptr : UInt256)
    (spender : AccountAddress) (value : UInt256) : ByteArray :=
  allocatedWordCallMemory mem ptr constructorApproveSelectorWord [UInt256.ofNat spender.val, value]

theorem constructorApproveMemory_buffer (mem : ByteArray) (ptr : UInt256)
    (spender : AccountAddress) (value : UInt256) (hlo : 96 ≤ ptr.toNat) :
    BytesBuffer (constructorApproveMemory mem ptr spender value) ptr
      (constructorApproveCalldata spender value) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [constructorApproveCalldata_size, constructorApproveMemory,
      allocatedWordCallMemory_size _ _ _ (words := [UInt256.ofNat spender.val, value]) (by simp)]
    simp only [List.length_cons, List.length_nil]; omega
  · rw [constructorApproveCalldata_size]
    exact allocatedWordCallMemory_length _ _ _ (words := [UInt256.ofNat spender.val, value]) (by simp) hlo
  · have hr := allocatedWordCallMemory_read mem ptr constructorApproveSelectorWord
      (words := [UInt256.ofNat spender.val, value]) (by simp) hlo
    change (constructorApproveMemory mem ptr spender value).readWithPadding (ptr.toNat + 32) 68 =
      constructorApproveSelectorWord.toByteArray.extract 0 4 ++
        wordBytes [UInt256.ofNat spender.val, value] at hr
    rw [constructorApproveCalldata_size, hr,
      show constructorApproveSelectorWord.toByteArray.extract 0 4 = constructorApproveSelector from
        by decide +kernel]
    simp only [constructorApproveCalldata, wordBytes, ByteArray.append_empty]

theorem constructorApproveMemory_free (mem : ByteArray) (ptr : UInt256)
    (spender : AccountAddress) (value : UInt256) :
    memLoad ⟨64⟩ (constructorApproveMemory mem ptr spender value) = nextCursor ptr ⟨100⟩ :=
  allocatedWordCallMemory_free _ _ _ _

theorem constructorApproveMemory_prefix (mem : ByteArray) (ptr : UInt256)
    (spender : AccountAddress) (value : UInt256) :
    MemoryPrefix mem (constructorApproveMemory mem ptr spender value) ptr.toNat :=
  allocatedWordCallMemory_prefix _ _ _ _

end Benchmarks.Morpho.MetaMorphoV1_1
