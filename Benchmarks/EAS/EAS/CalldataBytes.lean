import Benchmarks.EAS.EAS.CalldataRead
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: taking a prefix of a padded list slice.
theorem paddedList_take {α : Type} (xs : List α) (a : α) (m n : Nat) (h : n ≤ m) :
    (xs.take m ++ List.replicate (m-(xs.take m).length) a).take n =
      xs.take n ++ List.replicate (n-(xs.take n).length) a := by
  simp only [List.take_append,List.take_take,List.take_replicate,List.length_take,Nat.min_eq_left h]
  congr 2
  omega

-- LIBRARY CANDIDATE: dropping a prefix of a padded list slice.
theorem paddedList_drop {α : Type} (xs : List α) (a : α) (m n : Nat) (h : n ≤ m) :
    (xs.take m ++ List.replicate (m-(xs.take m).length) a).drop n =
      (xs.drop n).take (m-n) ++ List.replicate ((m-n)-((xs.drop n).take (m-n)).length) a := by
  simp only [List.drop_append,List.drop_take,List.drop_replicate,List.length_take,List.length_drop]
  congr 2
  omega

-- GENERALIZES decodeABIValue_legacyBytes_ok to every mode with the same byte payload semantics.
theorem decodeBytes_payload {bytes : List UInt8} {start len : Nat} {mode : DecodeMode}
    (hr : readNat? bytes start = some len) (hl : len ≤ solcMaxLen mode)
    (hp : ((bytes.drop (start+32)).take len).length = len) :
    decodeABIValue? .bytes bytes start mode =
      some (.bytes ⟨((bytes.drop (start+32)).take len).toArray⟩,start+32+paddedSize len) := by
  unfold decodeABIValue?
  rw [hr]
  simp only [Option.bind,bind,show ¬ solcMaxLen mode < len by omega,if_false]
  rw [readBytes?,if_pos hp]

-- LIBRARY CANDIDATE: a padded CALLDATALOAD followed by its natural-address payload.
theorem decodePaddedBytes (cd : ByteArray) (start : UInt256)
    (hl : (calldataWord cd start.toNat).toNat ≤ solcMaxU64) :
    decodeABIValue? .bytes (solcReadBytes cd.toList start.toNat
        (32+(calldataWord cd start.toNat).toNat)) 0 =
      some (.bytes (cd.readBytes (start.toNat+32) (calldataWord cd start.toNat).toNat),
        32+paddedSize (calldataWord cd start.toNat).toNat) := by
  let len := (calldataWord cd start.toNat).toNat
  let input := solcReadBytes cd.toList start.toNat (32+len)
  have hs : start.toNat % EVM.wordModulus = start.toNat := Nat.mod_eq_of_lt start.val.isLt
  have htake : input.take 32 = EVM.Word.toBytesBE (calldataWord cd start.toNat) := by
    change (solcReadBytes cd.toList start.toNat (32+len)).take 32 = _
    rw [solcReadBytes,hs,paddedList_take _ _ _ _ (by omega)]
    simpa only [solcReadBytes,hs] using solcReadBytes_word_total cd start
  have hdrop : input.drop 32 = (cd.readBytes (start.toNat+32) len).toList := by
    rw [show input = solcReadBytes cd.toList start.toNat (32+len) from rfl,
      solcReadBytes,hs,paddedList_drop _ _ _ _ (by omega),readBytes_padded_toList,
      List.drop_drop,Nat.add_sub_cancel_left]
  have hlen : (cd.readBytes (start.toNat+32) len).toList.length = len := by
    rw [readBytes_padded_toList,List.length_append,List.length_replicate,List.length_take,List.length_drop]
    omega
  have hr : readNat? input 0 = some len := by
    simp only [readNat?,readWord?,readBytes?,List.drop_zero,htake,word_toBytesBE_length_32,
      if_true,bind,Option.bind,bytesToWord_toBytesBE]
    rfl
  have hd : (input.drop (0+32)).take len = (cd.readBytes (start.toNat+32) len).toList := by
    rw [Nat.zero_add,hdrop,List.take_of_length_le (by omega)]
  have he := decodeBytes_payload (mode := .modern) hr hl (by rw [hd,hlen])
  rw [hd] at he
  have hb : (⟨(cd.readBytes (start.toNat+32) len).toList.toArray⟩ : ByteArray) =
      cd.readBytes (start.toNat+32) len := by
    apply byteArray_eq_of_toList_eq
    simp only [byteArray_toList_eq,List.toList_toArray]
  simpa only [hb,Nat.zero_add] using he

end Benchmarks.EAS.EAS
