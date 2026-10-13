import Benchmarks.CurveVault.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

-- GENERALIZES Reasoning.ABI.decodeScalarWords_address_address_none_short — any scalar list.
theorem decodeScalarWords_none_short (types : List ABIType) (bytes : List UInt8) (cursor : Nat)
    (hcursor : cursor ≤ bytes.length) (hshort : bytes.length < cursor + 32 * types.length) :
    decodeScalarWords? types bytes cursor = none := by
  induction types generalizing cursor with
  | nil => simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hshort; omega
  | cons ty tys ih =>
    rw [decodeScalarWords?]
    by_cases hhead : bytes.length < cursor + 32
    · have hlen : ¬ ((bytes.drop cursor).take 32).length = 32 := by
        simp only [List.length_take, List.length_drop]; omega
      simp only [decodeScalarWord?, readWord?, readBytes?, hlen, ↓reduceIte, Option.bind, bind]
    · have ht : decodeScalarWords? tys bytes (cursor + 32) = none :=
        ih _ (by omega) (by simp only [List.length_cons] at hshort; omega)
      rw [ht]
      cases decodeScalarWord? ty bytes cursor <;> simp

-- LIBRARY CANDIDATE: a complete canonical address word, at an arbitrary calldata offset.
theorem decodeScalarWord_calldata_address (cd : ByteArray) (off : Nat)
    (hoff : 4 + off < 2 ^ 64) (hfull : off + 36 ≤ cd.size) :
    decodeScalarWord? (.elem .address) (cd.toList.drop 4) off =
      if (calldataWord cd (4 + off)).toNat < EVM.addressModulus then
        some (.address (AccountAddress.ofNat (calldataWord cd (4 + off)).toNat), off + 32)
      else none := by
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen : (((cd.toList.drop 4).drop off).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, htlen]; omega
  have hword : ABI.bytesToWord (((cd.toList.drop 4).drop off).take 32) = calldataWord cd (4 + off) := by
    simpa only [List.drop_drop] using decode_word_at_eq cd (4 + off) (by omega) hoff
  by_cases hc : (calldataWord cd (4 + off)).toNat < EVM.addressModulus
  · rw [if_pos hc, decodeScalarWord_address_ok hlen (by rw [hword]; exact hc), hword]
  · rw [if_neg hc, decodeScalarWord_address_none_noncanon hlen (by rw [hword]; exact hc)]

end Benchmarks.CurveVault
