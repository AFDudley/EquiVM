import Benchmarks.EAS.EAS.ScalarDecode
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000
open ABI.Solc08Calldata

-- LIBRARY CANDIDATE: decoding a sequence of ABI words at an arbitrary pre.
theorem decodeBytes32WordList (ws : List UInt256) (pre suffix : List UInt8) :
    decodeABIArrayStaticElems? abiBytes32 ws.length 32
      (pre ++ ws.flatMap EVM.Word.toBytesBE ++ suffix) pre.length =
      some (ws.map wordBytes32Value, pre.length + 32 * ws.length) := by
  induction ws generalizing pre with
  | nil => simp [decodeABIArrayStaticElems?]
  | cons w ws ih =>
    have hwlen : (EVM.Word.toBytesBE w).length = 32 := word_toBytesBE_length_32 w
    have hv : decodeABIValue? abiBytes32
        (pre ++ (w :: ws).flatMap EVM.Word.toBytesBE ++ suffix) pre.length =
        some (wordBytes32Value w, pre.length + 32) := by
      have ht : (((pre ++ (w :: ws).flatMap EVM.Word.toBytesBE ++ suffix).drop pre.length).take 32) =
          EVM.Word.toBytesBE w := by
        simp only [List.flatMap_cons, List.append_assoc, List.drop_left, List.take_append_of_le_length (by omega : 32 ≤ (EVM.Word.toBytesBE w).length)]
        rw [← hwlen, List.take_length]
      simpa only [ht] using (decodeABIValue_bytes32_ok (bytes := pre ++ (w :: ws).flatMap EVM.Word.toBytesBE ++ suffix)
        (start := pre.length) (by rw [ht]; exact hwlen))
    rw [List.length_cons, decodeABIArrayStaticElems?, hv]
    have hi := ih (pre ++ EVM.Word.toBytesBE w)
    simp only [List.length_append, hwlen, List.append_assoc] at hi
    simp only [bind, Option.bind, beq_self_eq_true, if_true, List.flatMap_cons,
      List.append_assoc, hi, List.map_cons, pure]
    congr 2
    omega

-- LIBRARY CANDIDATE: the calldata-reference reader agrees with CALLDATALOAD on a complete word.
theorem solcReadBytes_word {cd : ByteArray} {start : Nat}
    (hbound : start + 32 ≤ cd.size) (hsize : cd.size < UInt256.size) :
    solcReadBytes cd.toList start 32 = EVM.Word.toBytesBE (calldataWord cd start) := by
  have hs : start < EVM.wordModulus := by change start < UInt256.size; omega
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have ht : ((cd.toList.drop start).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]; omega
  simp only [solcReadBytes, Nat.mod_eq_of_lt hs, ht, Nat.sub_self, List.replicate_zero, List.append_nil]
  have hh := congrArg ByteArray.toList (calldataWord_bytes_at hbound)
  rw [← word_toBytesBE_toByteArray_eq_toByteArray] at hh
  simpa only [byteArray_toList_eq, List.toList_data_toByteArray, ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop, Nat.add_sub_cancel_left] using hh.symm

-- LIBRARY CANDIDATE: materialized bytes32 arrays retain their CALLDATALOAD words.
def calldataWordList (cd : ByteArray) (start count : Nat) : List UInt256 :=
  (List.range count).map (fun i => calldataWord cd (start + 32 * i))

theorem solcReadWords_flatMap {cd : ByteArray} {start count : Nat}
    (hbound : start + 32 * count ≤ cd.size) (hsize : cd.size < UInt256.size) :
    solcReadWords cd.toList start count = (calldataWordList cd start count).flatMap EVM.Word.toBytesBE := by
  unfold solcReadWords calldataWordList
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro i hi
  have hi' : i < count := List.mem_range.mp hi
  have hw : start + 32 * i + 32 ≤ cd.size := by omega
  have hs : start + 32 * i < EVM.wordModulus := by change start + 32 * i < UInt256.size; omega
  simp only [solcAdd, Nat.mod_eq_of_lt hs, Function.comp_apply]
  exact solcReadBytes_word hw hsize

theorem decodeSolcReadWords {cd : ByteArray} {start count : Nat}
    (hbound : start + 32 * count ≤ cd.size) (hsize : cd.size < UInt256.size) :
    decodeABIArrayStaticElems? abiBytes32 count 32 (solcReadWords cd.toList start count) 0 =
      some ((calldataWordList cd start count).map wordBytes32Value, 32 * count) := by
  rw [solcReadWords_flatMap hbound hsize]
  simpa only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add,
    calldataWordList, List.length_map, List.length_range] using
    (decodeBytes32WordList (calldataWordList cd start count) [] [])

theorem solcReadNat_word {cd : ByteArray} {start : Nat}
    (hbound : start + 32 ≤ cd.size) (hsize : cd.size < UInt256.size) :
    solcReadNat cd.toList start = (calldataWord cd start).toNat := by
  rw [solcReadNat, solcReadBytes_word hbound hsize, bytesToWord_toBytesBE]

-- LIBRARY CANDIDATE: this mode ignores the modern decoder's separate total-size guard.
theorem decodeCalldataSolc08 (table : List (Nat × List CalldataPlan))
    (names : List Ident) (types : List ABIType) (cd : ByteArray) :
    decodeCalldataWithMode (.solc08Calldata table) names types cd =
      if cd.size < 4 then none else
        (decodeArgs? table types cd).bind (fun vs => decodeCalldata.insertValues names vs ∅) := by
  have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  simp only [decodeCalldataWithMode, decodeCalldata, hlen]
  split
  · rfl
  · split <;> rfl

theorem decodeWordArrayValue_eq (bytes : List UInt8) (start : Nat) :
    decodeValue? (.dynamicArray abiBytes32) bytes start {} false =
      if solcMaxU64 < solcReadNat bytes start || badExtent true false bytes start (solcReadNat bytes start) 32 then none else
        (decodeABIArrayStaticElems? abiBytes32 (solcReadNat bytes start) 32
          (solcReadWords bytes (solcAdd start 32) (solcReadNat bytes start)) 0).map
            (fun p => Value.array p.1) := by
  rw [decodeValue?]
  simp only [show stride? abiBytes32 = some 32 from rfl, bind, Option.bind]
  change (if solcMaxU64 < solcReadNat bytes start || badExtent true false bytes start (solcReadNat bytes start) 32 then none else
    (decodeABIArrayStaticElems? abiBytes32 (solcReadNat bytes start) 32
      (solcReadWords bytes (solcAdd start 32) (solcReadNat bytes start * 32 / 32)) 0).bind
        (fun p => some (Value.array p.1))) = _
  rw [Nat.mul_div_cancel (solcReadNat bytes start) (by decide : 0 < 32)]
  split
  · rfl
  · cases decodeABIArrayStaticElems? abiBytes32 (solcReadNat bytes start) 32
      (solcReadWords bytes (solcAdd start 32) (solcReadNat bytes start)) 0 <;> rfl

-- LIBRARY CANDIDATE: the exact guards of the top-level solc bytes32-array decoder.
theorem decodeWordArray_eq {cd : ByteArray} (name : Ident) (table : List (Nat × List CalldataPlan))
    (h4 : 4 ≤ cd.size)
    (hhead : solcSLT (solcSub cd.size 4) 32 = false)
    (hplans : ((table.find? (fun entry => entry.1 == (bytesToWord (cd.toList.take 4)).toNat)).map Prod.snd).getD [] = []) :
    decodeCalldataWithMode (.solc08Calldata table) [name] [.dynamicArray abiBytes32] cd =
      if solcMaxU64 < solcReadNat cd.toList 4 then none else
        let start := solcAdd 4 (solcReadNat cd.toList 4)
        let size := solcReadNat cd.toList start
        if solcMaxU64 < size || badExtent true false cd.toList start size 32 then none else
          (decodeABIArrayStaticElems? abiBytes32 size 32
            (solcReadWords cd.toList (solcAdd start 32) size) 0).map
              (fun p => (∅ : Store).insert name (.array p.1)) := by
  rw [decodeCalldataSolc08, if_neg (by omega : ¬ cd.size < 4)]
  simp only [decodeArgs?, List.isEmpty_cons, Bool.false_eq_true, if_false,
    show abiTupleHeadSize? [.dynamicArray abiBytes32] = some 32 from by native_decide,
    bind, Option.bind, hhead, hplans]
  simp only [decodeFields?, stride?, isDynamicABIType, if_true, if_false,
    List.headD_nil, retainFailure, List.contains_nil, Bool.false_eq_true,
    solcTailTarget?, Bool.not_true, show solcAdd 4 0 = 4 from rfl,
    bind, Option.bind, Bool.true_and, Bool.and_false]
  by_cases ho : solcMaxU64 < solcReadNat cd.toList 4
  · simp only [ho, if_true, Option.bind_none]
  · simp only [ho, if_false]
    rw [decodeWordArrayValue_eq]
    cases hb : (decide (solcMaxU64 < solcReadNat cd.toList (solcAdd 4 (solcReadNat cd.toList 4))) ||
        badExtent true false cd.toList (solcAdd 4 (solcReadNat cd.toList 4))
          (solcReadNat cd.toList (solcAdd 4 (solcReadNat cd.toList 4))) 32)
    · simp only [hb, Bool.false_eq_true, if_false]
      cases decodeABIArrayStaticElems? abiBytes32 (solcReadNat cd.toList (solcAdd 4 (solcReadNat cd.toList 4))) 32
        (solcReadWords cd.toList (solcAdd (solcAdd 4 (solcReadNat cd.toList 4)) 32)
          (solcReadNat cd.toList (solcAdd 4 (solcReadNat cd.toList 4)))) 0 <;> rfl
    · rfl

-- LIBRARY CANDIDATE: signed comparison with a nonnegative left operand.
theorem solcSLT_smallLeft {a b : Nat} (ha : a < 2^255) (hb : b < UInt256.size) :
    solcSLT a b = decide (a < b ∧ b < 2^255) := by
  unfold solcSLT
  change decide ((if (UInt256.ofNat a).toNat < 2^255 then ((UInt256.ofNat a).toNat : Int)
      else ((UInt256.ofNat a).toNat : Int) - 2^256) <
    (if (UInt256.ofNat b).toNat < 2^255 then ((UInt256.ofNat b).toNat : Int)
      else ((UInt256.ofNat b).toNat : Int) - 2^256)) = _
  rw [ofNat_toNat_lt a (by change a < 2^256; omega), ofNat_toNat_lt b hb, if_pos ha]
  by_cases hb' : b < 2^255
  · simp only [hb', if_true, and_true, Int.ofNat_lt]
  · simp only [hb', if_false, and_false, decide_false]
    apply decide_eq_false
    change b < 2^256 at hb
    omega

-- LIBRARY CANDIDATE: the signed top-level ABI head check fails before decoding any argument.
theorem decodeSolc_none_head {cd : ByteArray} (names : List Ident) (types : List ABIType)
    (table : List (Nat × List CalldataPlan)) (head : Nat) (hne : types.isEmpty = false)
    (ht : abiTupleHeadSize? types = some head)
    (h4 : 4 ≤ cd.size) (hhead : solcSLT (solcSub cd.size 4) head = true) :
    decodeCalldataWithMode (.solc08Calldata table) names types cd = none := by
  rw [decodeCalldataSolc08,if_neg (by omega : ¬ cd.size < 4)]
  simp only [decodeArgs?,hne,Bool.false_eq_true,if_false,ht,bind,Option.bind,hhead,if_true]

theorem decodeWordArray_none_head {cd : ByteArray} (name : Ident) (table : List (Nat × List CalldataPlan))
    (h4 : 4 ≤ cd.size) (hhead : solcSLT (solcSub cd.size 4) 32 = true) :
    decodeCalldataWithMode (.solc08Calldata table) [name] [.dynamicArray abiBytes32] cd = none :=
  decodeSolc_none_head [name] [.dynamicArray abiBytes32] table 32 rfl (by native_decide) h4 hhead

end Benchmarks.EAS.EAS
