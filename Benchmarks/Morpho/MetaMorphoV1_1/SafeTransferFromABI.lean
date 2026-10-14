import Benchmarks.Morpho.MetaMorphoV1_1.SafeTransferABI
import Benchmarks.Morpho.MetaMorphoV1_1.EncodedWordCallMemory

/-! The three-word transferFrom request used by ERC4626 deposits. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def safeTransferFromSelector : ByteArray := ⟨#[0x23, 0xb8, 0x72, 0xdd]⟩

def safeTransferFromSelectorWord : UInt256 := UInt256.shiftLeft ⟨599290589⟩ ⟨224⟩

def safeTransferFromWords (sender recipient : AccountAddress) (amount : UInt256) : List UInt256 :=
  [UInt256.ofNat sender.toNat, UInt256.ofNat recipient.toNat, amount]

def safeTransferFromCalldata (sender recipient : AccountAddress) (amount : UInt256) : ByteArray :=
  safeTransferFromSelector ++ wordBytes (safeTransferFromWords sender recipient amount)

theorem safeTransferFromCalldata_size (sender recipient : AccountAddress) (amount : UInt256) :
    (safeTransferFromCalldata sender recipient amount).size = 100 := by
  simp only [safeTransferFromCalldata, ByteArray.size_append, wordBytes_size,
    safeTransferFromWords, List.length_cons, List.length_nil]
  rfl

theorem safeTransferFromEncode (sender recipient : AccountAddress) (amount : UInt256) :
    config.externalABI.encode? "transferFrom" [.address sender, .address recipient, uint256Value amount] =
      some (safeTransferFromCalldata sender recipient amount) := by
  change encodeCallWithSelector?
    (ByteArray.mk ((EVM.Word.ofNat 0x23b872dd).toBytesBE.drop 28).toArray)
    [abiAddress, abiAddress, abiUInt256] [.address sender, .address recipient, uint256Value amount] = _
  rw [show ByteArray.mk ((EVM.Word.ofNat 0x23b872dd).toBytesBE.drop 28).toArray =
    safeTransferFromSelector by decide +kernel]
  have hh : abiTupleHeadSize? [abiAddress, abiAddress, abiUInt256] = some 96 := by
    simp [abiTupleHeadSize?, isDynamicABIType, staticABIEncodedSize?, abiAddress, abiUInt256]
  rw [encodeCallWithSelector?, encodeABIValues?, hh]
  simp only [encodeABIValuesFrom?, encodeAddressWord, encodeABIValue_uint256_word,
    show isDynamicABIType abiAddress = false from rfl,
    show isDynamicABIType abiUInt256 = false from rfl,
    bind, Option.bind, Bool.false_eq_true, if_false, List.nil_append, List.append_nil,
    List.toByteArray_append, byteArray_toList_toByteArray, safeTransferFromCalldata,
    safeTransferFromWords, wordBytes, ByteArray.append_empty, ByteArray.append_assoc]

theorem safeTransferFromMemory_read (mem : ByteArray) (ptr : UInt256)
    (sender recipient : AccountAddress) (amount : UInt256) (hlo : 96 ≤ ptr.toNat)
    (hptr : ptr.toNat < 2 ^ 64) :
    (allocatedWordCallMemory mem ptr safeTransferFromSelectorWord
      (safeTransferFromWords sender recipient amount)).readWithPadding
        (ptr + UInt256.ofNat 32).toNat 100 = safeTransferFromCalldata sender recipient amount := by
  rw [uadd_word_ofNat_toNat ptr 32 (by change _ < 2 ^ 256; omega)]
  have h := allocatedWordCallMemory_read mem ptr safeTransferFromSelectorWord
    (words := safeTransferFromWords sender recipient amount) (by simp [safeTransferFromWords]) hlo
  rw [show safeTransferFromSelectorWord.toByteArray.extract 0 4 = safeTransferFromSelector by decide +kernel] at h
  exact h

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
