import Benchmarks.CurveVault.Common

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: Vyper calldata with a uint256 followed by an address.
theorem decodeCalldata_vyper_uint256_address_ok {cd : ByteArray} {x y : Ident}
    (hsize : 68 ≤ cd.size) (hcanon : (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldataWithMode .vyper [x, y] [abiUInt256, .elem .address] cd =
      some (((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen0 : (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
    simp only [List.drop_zero, List.length_take, List.length_drop, htlen]; omega
  have hlen32 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, htlen]; omega
  have hword0 : ABI.bytesToWord (((cd.toList.drop 4).drop 0).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  have hword32 : ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) = calldataWord cd 36 := by
    simpa only [List.drop_drop] using decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hdecode : decodeScalarWords? [abiUInt256, .elem .address] (cd.toList.drop 4) 0 =
      some [.int (Int.ofNat (calldataWord cd 4).toNat), .address (AccountAddress.ofNat (calldataWord cd 36).toNat)] := by
    simp only [decodeScalarWords?, Nat.zero_add]
    rw [decodeScalarWord_uint256_ok hlen0]
    simp only [Option.bind, bind, Nat.zero_add]
    rw [decodeScalarWord_address_ok hlen32 (by rw [hword32]; exact hcanon)]
    simp only [Option.bind, bind, hword0, hword32]
  rw [decodeCalldataWithMode_vyperScalarWords_eq (by decide +kernel)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4), hdecode]
  rfl

-- LIBRARY CANDIDATE: the address word is rejected even with an arbitrary uint256 prefix.
theorem decodeCalldata_vyper_uint256_address_none_noncanon {cd : ByteArray} {x y : Ident}
    (hsize : 68 ≤ cd.size) (hcanon : ¬ (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldataWithMode .vyper [x, y] [abiUInt256, .elem .address] cd = none := by
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen0 : (((cd.toList.drop 4).drop 0).take 32).length = 32 := by
    simp only [List.drop_zero, List.length_take, List.length_drop, htlen]; omega
  have hlen32 : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, htlen]; omega
  have hword32 : ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32) = calldataWord cd 36 := by
    simpa only [List.drop_drop] using decode_word_at_eq cd 36 (by omega) (by norm_num)
  have hdecode : decodeScalarWords? [abiUInt256, .elem .address] (cd.toList.drop 4) 0 = none := by
    simp only [decodeScalarWords?, Nat.zero_add]
    rw [decodeScalarWord_uint256_ok hlen0]
    simp only [Option.bind, bind, Nat.zero_add]
    rw [decodeScalarWord_address_none_noncanon hlen32 (by rw [hword32]; exact hcanon)]
  rw [decodeCalldataWithMode_vyperScalarWords_eq (by decide +kernel)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4), hdecode]

-- LIBRARY CANDIDATE: either truncated word rejects this two-word Vyper entry.
theorem decodeCalldata_vyper_uint256_address_none_short {cd : ByteArray} {x y : Ident}
    (hsize : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode .vyper [x, y] [abiUInt256, .elem .address] cd = none := by
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hdecode : decodeScalarWords? [abiUInt256, .elem .address] (cd.toList.drop 4) 0 = none := by
    simp only [decodeScalarWords?, Nat.zero_add]
    by_cases hfirst : cd.size < 36
    · rw [decodeScalarWord_uint256_none_short (by
        simp only [List.drop_zero, List.length_take, List.length_drop, htlen]; omega)]
      rfl
    · rw [decodeScalarWord_uint256_ok (by
        simp only [List.drop_zero, List.length_take, List.length_drop, htlen]; omega)]
      simp only [Option.bind, bind, Nat.zero_add]
      rw [decodeScalarWord_address_none_short (by
        simp only [List.length_take, List.length_drop, htlen]; omega)]
  rw [decodeCalldataWithMode_vyperScalarWords_eq (by decide +kernel)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4), hdecode]

end Benchmarks.CurveVault
