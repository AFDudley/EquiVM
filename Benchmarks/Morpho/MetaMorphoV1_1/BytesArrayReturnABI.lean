import Benchmarks.Morpho.MetaMorphoV1_1.Eip712ABI

/-! Canonical ABI offsets and payloads for a dynamic array of byte strings. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

-- LIBRARY CANDIDATE: dynamic byte-array ABI encoding, including its offset table.
def bytesArrayHeads (offset : Nat) : List ByteArray → ByteArray
  | [] => ByteArray.empty
  | b :: bs => (UInt256.ofNat offset).toByteArray ++
      bytesArrayHeads (offset + 32 + paddedSize b.size) bs

def bytesArrayTails : List ByteArray → ByteArray
  | [] => ByteArray.empty
  | b :: bs => stringPayloadBytes b ++ bytesArrayTails bs

def bytesArrayReturnBytes (bs : List ByteArray) : ByteArray :=
  (⟨32⟩ : UInt256).toByteArray ++ ((UInt256.ofNat bs.length).toByteArray ++
    (bytesArrayHeads (32 * bs.length) bs ++ bytesArrayTails bs))

theorem bytesArrayHeads_size (offset : Nat) (bs : List ByteArray) :
    (bytesArrayHeads offset bs).size = 32 * bs.length := by
  induction bs generalizing offset with
  | nil => rfl
  | cons b bs ih =>
      simp only [bytesArrayHeads, ByteArray.size_append, toByteArray_size, ih, List.length_cons]
      omega

theorem bytesArrayTails_size_cons (b : ByteArray) (bs : List ByteArray) :
    (bytesArrayTails (b :: bs)).size = 32 + paddedSize b.size + (bytesArrayTails bs).size := by
  rw [bytesArrayTails, ByteArray.size_append, stringPayloadBytes_size]

theorem bytesArrayReturnBytes_size (bs : List ByteArray) :
    (bytesArrayReturnBytes bs).size = 64 + 32 * bs.length + (bytesArrayTails bs).size := by
  simp only [bytesArrayReturnBytes, ByteArray.size_append, toByteArray_size, bytesArrayHeads_size]
  omega

theorem encodeABIBytesPayload (bytes : ByteArray) :
    encodeABIValue? .bytes (.bytes bytes) = some (stringPayloadBytes bytes).toList := by
  have h := encodeABIStringPayload bytes
  simpa only [encodeABIValue?] using h

theorem bytesArrayEncodeFrom (bs : List ByteArray) (headSize : Nat) (head tail : List UInt8) :
    encodeABIDynamicArrayElemsFrom? .bytes (bs.map Value.bytes) headSize head tail =
      some (head ++ (bytesArrayHeads (headSize + tail.length) bs).toList ++
        tail ++ (bytesArrayTails bs).toList) := by
  induction bs generalizing head tail with
  | nil => simp only [List.map_nil, encodeABIDynamicArrayElemsFrom?, bytesArrayHeads,
      bytesArrayTails, show ByteArray.empty.toList = [] by simp [byteArray_toList_eq], List.append_nil]
  | cons b bs ih =>
      have hl : (stringPayloadBytes b).toList.length = 32 + paddedSize b.size := by
        rw [byteArray_toList_eq, Array.length_toList]
        exact stringPayloadBytes_size b
      rw [List.map_cons, encodeABIDynamicArrayElemsFrom?, encodeABIBytesPayload]
      simp only [bind, Option.bind]
      rw [ih]
      simp only [bytesArrayHeads, bytesArrayTails, byteArray_toList_append, List.append_assoc,
        List.length_append, hl, natBytes, EVM.Word.ofNat, word_toBytesBE_eq_toByteArray_toList]
      rw [show headSize + (tail.length + (32 + paddedSize b.size)) =
        headSize + tail.length + 32 + paddedSize b.size by omega]

theorem bytesArrayReturnEncoding (bs : List ByteArray) :
    encodeReturnValue? (.dynamicArray .bytes) (.array (bs.map Value.bytes)) =
      some (bytesArrayReturnBytes bs) := by
  have hd : encodeABIValue? (.dynamicArray .bytes) (.array (bs.map Value.bytes)) =
      some (natBytes bs.length ++
        (bytesArrayHeads (32 * bs.length) bs ++ bytesArrayTails bs).toList) := by
    simp only [encodeABIValue?, encodeABIArrayElems?, isDynamicABIType, if_true,
      List.length_map, bytesArrayEncodeFrom, List.length_nil, Nat.add_zero, List.nil_append,
      List.append_nil, bind, Option.bind, byteArray_toList_append, Nat.mul_comm]
  have hh : abiTupleHeadSize? [.dynamicArray .bytes] = some 32 := by
    simp only [abiTupleHeadSize?, isDynamicABIType, if_true, bind, Option.bind]
  simp only [encodeReturnValue?, encodeReturnValues?, encodeABIValues?, hh,
    encodeABIValuesFrom?, hd, isDynamicABIType, if_true, bind, Option.bind,
    List.length_nil, Nat.add_zero, List.nil_append, List.append_nil]
  rw [mk_toArray_eq]
  simp only [List.toByteArray_append, natBytes_toByteArray, byteArray_toList_toByteArray,
    bytesArrayReturnBytes]
  rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
