import Benchmarks.Morpho.MetaMorphoV1_1.CalldataReference

/-! Padded byte payloads read by the calldata-reference decoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory ABI.Solc08Calldata

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false
set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: taking or dropping a prefix of a zero-padded list slice.
theorem paddedList_take {α : Type} (xs : List α) (a : α) (m n : Nat) (h : n ≤ m) :
    (xs.take m ++ List.replicate (m - (xs.take m).length) a).take n =
      xs.take n ++ List.replicate (n - (xs.take n).length) a := by
  simp only [List.take_append, List.take_take, List.take_replicate, List.length_take,
    Nat.min_eq_left h]
  congr 2
  omega

theorem paddedList_drop {α : Type} (xs : List α) (a : α) (m n : Nat) (h : n ≤ m) :
    (xs.take m ++ List.replicate (m - (xs.take m).length) a).drop n =
      (xs.drop n).take (m - n) ++
        List.replicate ((m - n) - ((xs.drop n).take (m - n)).length) a := by
  simp only [List.drop_append, List.drop_take, List.drop_replicate,
    List.length_take, List.length_drop]
  congr 2
  omega

-- LIBRARY CANDIDATE: a padded payload has exactly the requested byte length.
theorem readBytes_padded_size (cd : ByteArray) (start len : Nat) :
    (cd.readBytes start len).size = len := by
  have h := congrArg List.length (readBytes_padded_toList cd start len)
  simp only [byteArray_toList_eq, Array.length_toList, List.length_append,
    List.length_take, List.length_drop, List.length_replicate] at h
  change (cd.readBytes start len).size = _ at h
  omega

-- LIBRARY CANDIDATE: decode a length-prefixed payload produced by the padded API reader.
theorem decodeSolcPaddedBytes (cd : ByteArray) (start : UInt256)
    (hl : (calldataWord cd start.toNat).toNat ≤ solcMaxU64) :
    decodeABIValue? .bytes (solcReadBytes cd.toList start.toNat
      (32 + (calldataWord cd start.toNat).toNat)) 0 =
        some (.bytes (cd.readBytes (start.toNat + 32) (calldataWord cd start.toNat).toNat),
          32 + paddedSize (calldataWord cd start.toNat).toNat) := by
  let len := (calldataWord cd start.toNat).toNat
  let input := solcReadBytes cd.toList start.toNat (32 + len)
  have hmod : start.toNat % EVM.wordModulus = start.toNat := Nat.mod_eq_of_lt start.val.isLt
  have ht : input.take 32 = solcReadBytes cd.toList start.toNat 32 := by
    dsimp only [input]
    simp only [solcReadBytes, hmod]
    exact paddedList_take _ _ _ _ (by omega)
  have htlen : (input.take 32).length = 32 := by
    rw [ht]
    simp only [solcReadBytes, List.length_append, List.length_replicate,
      List.length_take, List.length_drop]
    omega
  have hr : readNat? input 0 = some len := by
    simp only [readNat?, readWord?, readBytes?, List.drop_zero, htlen, if_true,
      bind, Option.bind]
    rw [ht]
    exact congrArg some (solcReadNat_word_total cd start)
  have hd : input.drop 32 = (cd.readBytes (start.toNat + 32) len).toList := by
    dsimp only [input]
    rw [solcReadBytes, hmod, paddedList_drop _ _ _ _ (by omega),
      readBytes_padded_toList, List.drop_drop, Nat.add_sub_cancel_left]
  have hp : (input.drop 32).take len = (cd.readBytes (start.toNat + 32) len).toList := by
    rw [hd, List.take_of_length_le (by
      rw [byteArray_toList_eq, Array.length_toList]
      exact le_of_eq (readBytes_padded_size _ _ _))]
  change decodeABIValue? .bytes input 0 = _
  rw [decodeABIValue?, hr]
  simp only [show ¬ solcMaxLen .modern < len by exact Nat.not_lt.mpr hl,
    bind, Option.bind, if_false, Nat.zero_add]
  rw [readBytes?, hp]
  have hs : (cd.readBytes (start.toNat + 32) len).toList.length = len := by
    rw [byteArray_toList_eq, Array.length_toList]
    exact readBytes_padded_size _ _ _
  rw [if_pos hs]
  have hb : (⟨(cd.readBytes (start.toNat + 32) len).toList.toArray⟩ : ByteArray) =
      cd.readBytes (start.toNat + 32) len := by
    apply byteArray_eq_of_toList_eq
    simp only [byteArray_toList_eq]
  simp only [hb, len]

-- LIBRARY CANDIDATE: zero-filling beyond calldata is valid at every EVM word address.
theorem calldataWord_zero_of_ge (cd : ByteArray) (start : UInt256)
    (h : cd.size ≤ start.toNat) : calldataWord cd start.toNat = ⟨0⟩ := by
  have hd : cd.toList.drop start.toNat = [] :=
    List.drop_eq_nil_of_le (by
      rw [byteArray_toList_eq, Array.length_toList]
      exact h)
  apply u256_inj
  rw [← solcReadNat_word_total]
  simp only [solcReadNat, solcReadBytes,
    Nat.mod_eq_of_lt (show start.toNat < EVM.wordModulus from start.val.isLt), hd,
    List.take_nil, List.length_nil, Nat.sub_zero, List.nil_append]
  decide +kernel

end Benchmarks.Morpho.MetaMorphoV1_1
