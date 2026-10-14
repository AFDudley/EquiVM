import Benchmarks.Morpho.MetaMorphoV1_1.Decode

/-! Scalar calldata decoding for an amount and two addresses. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: compose scalar decoders for uint256,address,address, including failures.
theorem decodeCalldata_uint256_address_address_result {cd : ByteArray} {x y z : Ident}
    (hlen : 100 ≤ cd.size) (hhi : cd.size < 2 ^ 255 + 4) :
    decodeCalldata [x, y, z] [abiUInt256, .elem .address, .elem .address] cd =
      if (calldataWord cd 36).toNat < EVM.addressModulus then
        if (calldataWord cd 68).toNat < EVM.addressModulus then
          some ((((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
            (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
              (.address (AccountAddress.ofNat (calldataWord cd 68).toNat)))
        else none
      else none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have h4 : (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, List.length_drop, htlen]; omega
  have h36 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
  have h68 : (((cd.toList.drop 4).drop 64).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, List.length_drop, htlen]; omega
  have hw4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hw36 : ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) =
      calldataWord cd 36 := by
    simpa only [List.drop_drop] using decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hw68 : ABI.bytesToWord (((cd.toList.drop 4).drop 64).take 32) =
      calldataWord cd 68 := by
    simpa only [List.drop_drop] using decode_word_at_eq cd 68 (by omega) (by norm_num)
  rw [decodeCalldata_scalarWords_eq (by decide)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by rintro ⟨_, hc⟩; rw [List.length_drop, htlen] at hc; omega)]
  simp only [decodeScalarWords?, decodeScalarWord_uint256_ok h4, bind, Option.bind,
    Nat.zero_add]
  by_cases hc1 : (calldataWord cd 36).toNat < EVM.addressModulus
  · rw [decodeScalarWord_address_ok h36 (by rw [hw36]; exact hc1), if_pos hc1]
    simp only [bind, Option.bind]
    by_cases hc2 : (calldataWord cd 68).toNat < EVM.addressModulus
    · rw [decodeScalarWord_address_ok h68 (by rw [hw68]; exact hc2), if_pos hc2]
      simp only [bind, Option.bind, List.drop_zero, decodeCalldata.insertValues, hw4, hw36, hw68]
    · rw [decodeScalarWord_address_none_noncanon h68 (by rw [hw68]; exact hc2), if_neg hc2]
  · rw [decodeScalarWord_address_none_noncanon h36 (by rw [hw36]; exact hc1), if_neg hc1]

end Benchmarks.Morpho.MetaMorphoV1_1
