import Benchmarks.Morpho.MetaMorphoV1_1.Common
import Reasoning.ABI

/-! The strict decimals return must contain a canonical uint8 word. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

-- LIBRARY CANDIDATE: a complete unsigned scalar return with its declared width check.
theorem decodeReturnUintBits (bits : BitWidth) {out : ByteArray} (hb : out.size < 2 ^ 255) :
    ABI.decodeReturnValues? [.elem (.int (.uint bits))] out =
      if 32 ≤ out.size ∧ (calldataWord out 0).toNat < EVM.twoPow bits.val then
        some [uint256Value (calldataWord out 0)] else none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeReturnValues_scalarWords_eq (by rfl)]
  rw [if_neg (by simp only [List.isEmpty_cons, hlen]; omega)]
  by_cases hl : 32 ≤ out.size
  · have h32 : ((out.toList.drop 0).take 32).length = 32 := by
      simp only [List.drop_zero, List.length_take, hlen]; omega
    rw [decodeScalarWords?, decodeScalarWord_uint_result bits h32,
      decode_word_at_eq_any out 0 (by omega)]
    by_cases hc : (calldataWord out 0).toNat < EVM.twoPow bits.val <;>
      simp only [if_pos, if_neg, hl, hc, and_self, true_and, not_false_eq_true,
        bind, Option.bind, decodeScalarWords?, pure]
  · have h32 : ¬ ((out.toList.drop 0).take 32).length = 32 := by
      simp only [List.drop_zero, List.length_take, hlen]; omega
    rw [if_neg (by omega)]
    simp only [decodeScalarWords?, decodeScalarWord?, readWord?, readBytes?, if_neg h32,
      bind, Option.bind]

theorem constructorStrictDecimalsDecode {out : ByteArray} (hb : out.size < 2 ^ 255) :
    config.externalABI.decode? "decimals" out =
      if 32 ≤ out.size ∧ (calldataWord out 0).toNat < 256 then
        some [uint256Value (calldataWord out 0)] else none := by
  change (ABI.decodeReturnValues? [.elem (.int (.uint ⟨8, by decide⟩))] out >>= fun vs => some vs) = _
  rw [decodeReturnUintBits _ hb]
  change ((if 32 ≤ out.size ∧ (calldataWord out 0).toNat < 256 then
    some [uint256Value (calldataWord out 0)] else none) >>= fun vs => some vs) = _
  split_ifs <;> rfl

end Benchmarks.Morpho.MetaMorphoV1_1
