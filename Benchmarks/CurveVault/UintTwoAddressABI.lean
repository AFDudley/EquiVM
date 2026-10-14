import Benchmarks.CurveVault.Common

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: Vyper scalar calldata with a uint256 and two addresses.
theorem decodeCalldata_vyper_uint256_address_address_eq {cd : ByteArray} {x y z : Ident}
    (hsize : 100 ≤ cd.size) :
    decodeCalldataWithMode .vyper [x, y, z] [abiUInt256, .elem .address, .elem .address] cd =
      if (calldataWord cd 36).toNat < EVM.addressModulus then
        if (calldataWord cd 68).toNat < EVM.addressModulus then
          some ((((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
            (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
            (.address (AccountAddress.ofNat (calldataWord cd 68).toNat)))
        else none
      else none := by
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hlen (off : Nat) (hoff : off ≤ 64) : (((cd.toList.drop 4).drop off).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, htlen]; omega
  have hword (off : Nat) (hoff : off ≤ 64) :
      ABI.bytesToWord (((cd.toList.drop 4).drop off).take 32) = calldataWord cd (4 + off) := by
    simpa only [List.drop_drop] using decode_word_at_eq cd (4 + off) (by omega) (by norm_num; omega)
  rw [decodeCalldataWithMode_vyperScalarWords_eq (by decide +kernel)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWords?, Nat.zero_add]
  rw [decodeScalarWord_uint256_ok (hlen 0 (by omega))]
  simp only [Option.bind, bind]
  by_cases hfirst : (calldataWord cd 36).toNat < EVM.addressModulus
  · rw [if_pos hfirst, decodeScalarWord_address_ok (hlen 32 (by omega))
      (by rw [hword 32 (by omega)]; exact hfirst)]
    simp only [Option.bind, bind]
    by_cases hlast : (calldataWord cd 68).toNat < EVM.addressModulus
    · rw [if_pos hlast, decodeScalarWord_address_ok (hlen 64 (by omega))
        (by rw [hword 64 (by omega)]; exact hlast)]
      simp only [Option.bind, bind, hword 0 (by omega), hword 32 (by omega), hword 64 (by omega)]
      rfl
    · rw [if_neg hlast, decodeScalarWord_address_none_noncanon (hlen 64 (by omega))
        (by rw [hword 64 (by omega)]; exact hlast)]
  · rw [if_neg hfirst, decodeScalarWord_address_none_noncanon (hlen 32 (by omega))
      (by rw [hword 32 (by omega)]; exact hfirst)]

theorem decodeCalldata_vyper_uint256_address_address_ok {cd : ByteArray} {x y z : Ident}
    (hsize : 100 ≤ cd.size)
    (hfirst : (calldataWord cd 36).toNat < EVM.addressModulus)
    (hlast : (calldataWord cd 68).toNat < EVM.addressModulus) :
    decodeCalldataWithMode .vyper [x, y, z] [abiUInt256, .elem .address, .elem .address] cd =
      some ((((∅ : Store).insert x (.int (Int.ofNat (calldataWord cd 4).toNat))).insert y
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))).insert z
        (.address (AccountAddress.ofNat (calldataWord cd 68).toNat))) := by
  rw [decodeCalldata_vyper_uint256_address_address_eq hsize, if_pos hfirst, if_pos hlast]

theorem decodeCalldata_vyper_uint256_address_address_none_noncanon0 {cd : ByteArray} {x y z : Ident}
    (hsize : 100 ≤ cd.size) (hfirst : ¬ (calldataWord cd 36).toNat < EVM.addressModulus) :
    decodeCalldataWithMode .vyper [x, y, z] [abiUInt256, .elem .address, .elem .address] cd = none := by
  rw [decodeCalldata_vyper_uint256_address_address_eq hsize, if_neg hfirst]

theorem decodeCalldata_vyper_uint256_address_address_none_noncanon1 {cd : ByteArray} {x y z : Ident}
    (hsize : 100 ≤ cd.size)
    (hfirst : (calldataWord cd 36).toNat < EVM.addressModulus)
    (hlast : ¬ (calldataWord cd 68).toNat < EVM.addressModulus) :
    decodeCalldataWithMode .vyper [x, y, z] [abiUInt256, .elem .address, .elem .address] cd = none := by
  rw [decodeCalldata_vyper_uint256_address_address_eq hsize, if_pos hfirst, if_neg hlast]

-- LIBRARY CANDIDATE: reject any truncated word in this Vyper scalar triple.
theorem decodeCalldata_vyper_uint256_address_address_none_short {cd : ByteArray} {x y z : Ident}
    (hsize : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldataWithMode .vyper [x, y, z] [abiUInt256, .elem .address, .elem .address] cd = none := by
  have htlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldataWithMode_vyperScalarWords_eq (by decide +kernel)]
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  simp only [decodeScalarWords?, Nat.zero_add]
  by_cases h36 : cd.size < 36
  · rw [decodeScalarWord_uint256_none_short (by
      simp only [List.length_take, List.length_drop, htlen]; omega)]
    rfl
  · rw [decodeScalarWord_uint256_ok (by
      simp only [List.length_take, List.length_drop, htlen]; omega)]
    simp only [Option.bind, bind]
    by_cases h68 : cd.size < 68
    · rw [decodeScalarWord_address_none_short (start := 32) (by
        simp only [List.length_take, List.length_drop, htlen]; omega)]
    · have hlen : (((cd.toList.drop 4).drop 32).take 32).length = 32 := by
        simp only [List.length_take, List.length_drop, htlen]; omega
      by_cases hc : (ABI.bytesToWord (((cd.toList.drop 4).drop 32).take 32)).toNat < EVM.addressModulus
      · rw [decodeScalarWord_address_ok hlen hc]
        simp only [Option.bind, bind]
        rw [decodeScalarWord_address_none_short (start := 64) (by
          simp only [List.length_take, List.length_drop, htlen]; omega)]
      · rw [decodeScalarWord_address_none_noncanon hlen hc]

end Benchmarks.CurveVault
