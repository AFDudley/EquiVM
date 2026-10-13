import Benchmarks.CurveVault.Calls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: Vyper returndata for any nonzero unsigned integer width.
theorem decodeReturn_vyper_uint_eq (bits : BitWidth) (out : ByteArray)
    (hbits : bits.val ≠ 0) (h32 : 32 ≤ out.size) :
    ABI.decodeReturnValueWithMode? .vyper (.elem (.int (.uint bits))) out =
      if (retWord out).toNat < 2 ^ bits.val then
        some (.int (Int.ofNat (retWord out).toNat)) else none := by
  have hlen : ((out.toList.drop 0).take 32).length = 32 := by
    simp only [List.drop_zero, List.length_take, byteArray_toList_eq, Array.length_toList]
    exact Nat.min_eq_left h32
  rw [decodeReturn_vyper_scalar _ _ rfl]
  simp only [decodeScalarWord?, ABI.readWord?, ABI.readBytes?, hlen, ↓reduceIte, Option.bind, bind]
  rw [bytesToWord_take32_retWord]
  simp only [ABI.decodeABIWord?, hbits, ↓reduceIte, EVM.twoPow]
  by_cases hc : (retWord out).toNat < 2 ^ bits.val
  all_goals
    simp only [show (retWord out).val.val = (retWord out).toNat from rfl, hc, ↓reduceIte]
    rfl

theorem decodeReturn_vyper_uint_short (bits : BitWidth) (out : ByteArray)
    (h32 : out.size < 32) :
    ABI.decodeReturnValueWithMode? .vyper (.elem (.int (.uint bits))) out = none := by
  have hlen : ¬ ((out.toList.drop 0).take 32).length = 32 := by
    simp only [List.drop_zero, List.length_take, byteArray_toList_eq, Array.length_toList]
    change ¬ min 32 out.size = 32
    omega
  rw [decodeReturn_vyper_scalar _ _ rfl]
  simp only [decodeScalarWord?, ABI.readWord?, ABI.readBytes?, hlen, ↓reduceIte, Option.bind, bind, Option.map_none]

-- GENERALIZES Reasoning.WordArithmetic.u256_shiftRight160_zero_of_lt.
theorem u256_shiftRight_zero_iff (w : UInt256) (bits : Nat) (hbits : bits < 256) :
    UInt256.shiftRight w (UInt256.ofNat bits) = ⟨0⟩ ↔ w.toNat < 2 ^ bits := by
  have hb : (UInt256.ofNat bits).toNat = bits := ulit_toNat' bits (by change bits < 2 ^ 256; omega)
  have hto : (UInt256.shiftRight w (UInt256.ofNat bits)).toNat = w.toNat / 2 ^ bits := by
    unfold UInt256.shiftRight
    rw [if_neg (by change ¬ (UInt256.ofNat bits).toNat ≥ 256; rw [hb]; omega)]
    change (w.val >>> (UInt256.ofNat bits).val).val = w.toNat / 2 ^ bits
    rw [Fin.shiftRight_val, Nat.shiftRight_eq_div_pow]
    change w.toNat / 2 ^ (UInt256.ofNat bits).toNat = w.toNat / 2 ^ bits
    rw [hb]
  constructor
  · intro h
    have hz := congrArg UInt256.toNat h
    rw [hto] at hz
    exact (Nat.div_eq_zero_iff.mp hz).resolve_left (by positivity)
  · intro h
    apply u256_inj
    change (UInt256.shiftRight w (UInt256.ofNat bits)).toNat = 0
    rw [hto, Nat.div_eq_of_lt h]

end Benchmarks.CurveVault
