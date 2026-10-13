import Benchmarks.EAS.EAS.StringDecode
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: a bounded signed extent check, including a head beyond the end.
theorem solcSLT_sub_small {size start need : Nat}
    (hs : size < 2^255) (hp : start < 2^255) (hn : need < 2^255) :
    solcSLT (solcSub size start) need = decide (size < start+need) := by
  have hsize : (UInt256.ofNat size).toNat = size := ulit_toNat' _ (by change size < 2^256; omega)
  have hstart : (UInt256.ofNat start).toNat = start := ulit_toNat' _ (by change start < 2^256; omega)
  have hneed : (UInt256.ofNat need).toNat = need := ulit_toNat' _ (by change need < 2^256; omega)
  unfold solcSLT solcSub
  change decide (EVM.signed (UInt256.ofNat (UInt256.sub (UInt256.ofNat size) (UInt256.ofNat start)).toNat) <
    EVM.signed (UInt256.ofNat need)) = _
  rw [u256_ofNat_toNat]
  change decide ((if (UInt256.sub (UInt256.ofNat size) (UInt256.ofNat start)).toNat < 2^255 then
    ((UInt256.sub (UInt256.ofNat size) (UInt256.ofNat start)).toNat : Int) else
    ((UInt256.sub (UInt256.ofNat size) (UInt256.ofNat start)).toNat : Int)-2^256) <
    (if (UInt256.ofNat need).toNat < 2^255 then ((UInt256.ofNat need).toNat : Int) else
    ((UInt256.ofNat need).toNat : Int)-2^256)) = _
  rw [hneed, if_pos hn]
  by_cases hp' : start ≤ size
  · rw [usub_toNat (by rw [hstart,hsize]; exact hp'), hsize, hstart, if_pos (by omega : size-start < 2^255)]
    congr 1
    apply propext
    omega
  · rw [usub_toNat_underflow (by rw [hstart,hsize]; omega), hsize, hstart]
    change decide ((if 2^256+size-start < 2^255 then ((2^256+size-start : Nat) : Int)
      else ((2^256+size-start : Nat) : Int)-2^256) < (need : Int)) = _
    rw [if_neg (by omega : ¬ 2^256+size-start < 2^255)]
    rw [decide_eq_true (by omega : size < start+need), decide_eq_true (by omega)]

-- LIBRARY CANDIDATE: reading a complete scalar word in the solc 0.8 materialized decoder.
theorem decodeSolcScalar {out : ByteArray} {start : Nat} {elem : ElemType}
    (hscalar : isABIScalarWordType (.elem elem) = true)
    (hh : start+32 ≤ out.size) (hb : out.size < UInt256.size) :
    decodeValue? (.elem elem) out.toList start {} = decodeABIWord? (.elem elem) (calldataWord out start) := by
  have ht : List.take 32 (EVM.Word.toBytesBE (calldataWord out start)) = EVM.Word.toBytesBE (calldataWord out start) :=
    List.take_of_length_le (by rw [word_toBytesBE_length_32])
  rw [decodeValue?, solcReadBytes_word hh hb, decodeABIValue_scalarWord_eq hscalar]
  simp only [decodeScalarWord?, readWord?, readBytes?, List.drop_zero,
    ht, word_toBytesBE_length_32,
    if_true, bind, Option.bind, bytesToWord_toBytesBE]
  cases decodeABIWord? (.elem elem) (calldataWord out start) <;> rfl

theorem decodeSolcBytes32 {out : ByteArray} {start : Nat}
    (hh : start+32 ≤ out.size) (hb : out.size < UInt256.size) :
    decodeValue? abiBytes32 out.toList start {} = some (wordBytes32Value (calldataWord out start)) := by
  rw [decodeValue?]
  have ht : List.take 32 (EVM.Word.toBytesBE (calldataWord out start)) = EVM.Word.toBytesBE (calldataWord out start) :=
    List.take_of_length_le (by rw [word_toBytesBE_length_32])
  rw [solcReadBytes_word hh hb, decodeABIValue_bytes32_ok (by
    rw [List.drop_zero, ht, word_toBytesBE_length_32])]
  simp only [Option.map_some, List.drop_zero,
    ht]

end Benchmarks.EAS.EAS
