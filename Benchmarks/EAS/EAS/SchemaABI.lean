import Benchmarks.EAS.EAS.ReturnWordDecode
import Benchmarks.EAS.EAS.GetSchemaSource
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def schemaTextStart (out : ByteArray) (base : Nat) : Nat := base+(calldataWord out (base+96)).toNat
def schemaTextLength (out : ByteArray) (base : Nat) : Nat := (calldataWord out (schemaTextStart out base)).toNat
def decodedSchemaRecord (out : ByteArray) (base : Nat) : SchemaRecord :=
  { uid := calldataWord out base
    resolver := AccountAddress.ofNat (calldataWord out (base+32)).toNat
    revocable := decide ((calldataWord out (base+64)).toNat ≠ 0)
    schema := out.extract (schemaTextStart out base+32) (schemaTextStart out base+32+schemaTextLength out base) }
def schemaBodyValid (out : ByteArray) (base : Nat) : Prop :=
  base+128 ≤ out.size ∧
  (calldataWord out (base+32)).toNat < EVM.addressModulus ∧
  ((calldataWord out (base+64)).toNat = 0 ∨ (calldataWord out (base+64)).toNat = 1) ∧
  (calldataWord out (base+96)).toNat ≤ solcMaxU64 ∧
  schemaTextStart out base+32 ≤ out.size ∧ schemaTextLength out base ≤ solcMaxU64 ∧
  schemaTextStart out base+32+schemaTextLength out base ≤ out.size
instance (out : ByteArray) (base : Nat) : Decidable (schemaBodyValid out base) := by
  unfold schemaBodyValid; infer_instance

theorem schemaFieldsDecode {out : ByteArray} {base : Nat}
    (hb : base+128 ≤ out.size) (hs : out.size < UInt256.size) :
    decodeFields? [abiBytes32,.elem .address,.elem .bool,.string] out.toList base 0 [{},{},{},{}] true = (do
      let a ← decodeABIWord? (.elem .address) (calldataWord out (base+32))
      let b ← decodeABIWord? (.elem .bool) (calldataWord out (base+64))
      let relative := (calldataWord out (base+96)).toNat
      if solcMaxU64 < relative then none else do
      let text ← decodeValue? .string out.toList (solcAdd base relative) {}
      some [wordBytes32Value (calldataWord out base),a,b,text]) := by
  have h0 : solcAdd base 0 = base := Nat.mod_eq_of_lt (by change base < UInt256.size; omega)
  have h32 : solcAdd base 32 = base+32 := Nat.mod_eq_of_lt (by change base+32 < UInt256.size; omega)
  have h64 : solcAdd base 64 = base+64 := Nat.mod_eq_of_lt (by change base+64 < UInt256.size; omega)
  have h96 : solcAdd base 96 = base+96 := Nat.mod_eq_of_lt (by change base+96 < UInt256.size; omega)
  simp only [decodeFields?, stride?, show isDynamicABIType abiBytes32 = false from rfl,
    show staticABIEncodedSize? abiBytes32 = some 32 from rfl, isDynamicABIType, staticABIEncodedSize?,
    bind, Option.bind, Bool.false_eq_true, if_false, if_true, List.headD_cons, List.tail_cons,
    retainFailure, List.contains_nil, Bool.not_true, Bool.false_and, Bool.true_and, solcTailTarget?,
    Nat.zero_add, h0, h32, h64, h96]
  rw [decodeSolcBytes32 (by omega) hs, decodeSolcScalar (by decide) (by omega) hs,
    decodeSolcScalar (by decide) (by omega) hs, solcReadNat_word (by omega) hs]
  cases ha : decodeABIWord? (.elem .address) (calldataWord out (base+32)) <;>
    cases hb' : decodeABIWord? (.elem .bool) (calldataWord out (base+64)) <;>
    simp only [Option.bind_some, Option.bind_none]
  by_cases ho : solcMaxU64 < (calldataWord out (base+96)).toNat
  · simp only [ho, if_true, Option.bind_none]
  · simp only [ho, if_false, Option.bind_some]
    cases decodeValue? .string out.toList (solcAdd base (calldataWord out (base+96)).toNat) {} <;> rfl

-- LIBRARY CANDIDATE: strict boolean-word decoding as a validity guard and value.
theorem decodeBoolWord_eq (w : UInt256) :
    decodeABIWord? (.elem .bool) w =
      if w.toNat = 0 ∨ w.toNat = 1 then some (.bool (decide (w.toNat ≠ 0))) else none := by
  change (if w.toNat = 0 then some (Value.bool false) else if w.toNat = 1 then some (Value.bool true) else none) = _
  by_cases h0 : w.toNat = 0 <;> by_cases h1 : w.toNat = 1 <;> simp only [h0,h1,if_true,if_false,
    true_or,false_or,or_true,or_self,ne_eq,Nat.one_ne_zero,not_true_eq_false,not_false_eq_true,decide_true,decide_false]

theorem decodeSchemaBody {out : ByteArray} {base : Nat}
    (hbase : base ≤ solcMaxU64) (hs : out.size < 2^255) :
    decodeValue? schemaRecordABI out.toList base {} =
      if schemaBodyValid out base then some (decodedSchemaRecord out base).tuple else none := by
  have hsize : out.size < UInt256.size := by change out.size < 2^256; omega
  have hbase' : base < 2^255 := by change base ≤ 18446744073709551615 at hbase; omega
  have hlen : out.toList.length = out.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [schemaRecordABI, decodeValue?]
  simp only [show abiTupleHeadSize? [abiBytes32,.elem .address,.elem .bool,.string] = some 128 by native_decide,
    show isDynamicABIType (.tuple [abiBytes32,.elem .address,.elem .bool,.string]) = true by native_decide,
    Bool.not_false, Bool.not_true, Bool.true_or, Bool.true_and, Bool.false_eq_true, if_false, bind, Option.bind, pure,
    show isMemory ({} : CalldataPlan) = true from rfl,
    show (List.range [abiBytes32,.elem .address,.elem .bool,.string].length).map
      (fun i => child ({} : CalldataPlan) (.field i)) = [{},{},{},{}] by native_decide]
  change (if solcSLT (solcSub out.toList.length base) 128 then none else
    (decodeFields? [abiBytes32,.elem .address,.elem .bool,.string] out.toList base 0 [{},{},{},{}] true).bind (fun vs => some (Value.tuple vs))) = _
  rw [hlen, solcSLT_sub_small hs hbase' (by decide)]
  by_cases hh : base+128 ≤ out.size
  · rw [decide_eq_false (by omega : ¬ out.size < base+128), if_neg (by decide : false ≠ true), schemaFieldsDecode hh hsize]
    have haddr : decodeABIWord? (.elem .address) (calldataWord out (base+32)) =
        if (calldataWord out (base+32)).toNat < EVM.addressModulus then
          some (.address (AccountAddress.ofNat (calldataWord out (base+32)).toNat)) else none := rfl
    rw [haddr, decodeBoolWord_eq]
    by_cases ha : (calldataWord out (base+32)).toNat < EVM.addressModulus
    · rw [if_pos ha]
      by_cases hc : (calldataWord out (base+64)).toNat = 0 ∨ (calldataWord out (base+64)).toNat = 1
      · rw [if_pos hc]
        simp only [bind, Option.bind]
        by_cases ho : (calldataWord out (base+96)).toNat ≤ solcMaxU64
        · rw [if_neg (by omega : ¬ solcMaxU64 < (calldataWord out (base+96)).toNat)]
          have hp : solcAdd base (calldataWord out (base+96)).toNat = schemaTextStart out base := by
            apply Nat.mod_eq_of_lt
            change base+(calldataWord out (base+96)).toNat < 2^256
            change base ≤ 18446744073709551615 at hbase
            change (calldataWord out (base+96)).toNat ≤ 18446744073709551615 at ho
            omega
          rw [hp, decodeSolcString (by
            unfold schemaTextStart
            change base ≤ 18446744073709551615 at hbase
            change (calldataWord out (base+96)).toNat ≤ 18446744073709551615 at ho
            omega) hs]
          simp only [schemaBodyValid, hh, ha, hc, ho, true_and,
            decodedSchemaRecord, SchemaRecord.tuple, schemaTextLength]
          split_ifs <;> rfl
        · simp only [show solcMaxU64 < (calldataWord out (base+96)).toNat by omega, if_true,
            schemaBodyValid, ho, false_and, and_false, if_false, Option.map_none, Option.bind_none]
      · simp only [hc, if_false, bind, Option.bind, Option.map_none,
          schemaBodyValid, hc, false_and, and_false, if_false]
    · simp only [ha, if_false, bind, Option.bind, Option.map_none,
        schemaBodyValid, ha, false_and, and_false, if_false]
  · simp only [show out.size < base+128 by omega, decide_true, if_true,
      schemaBodyValid, hh, false_and, if_false]

-- GENERALIZES the dynamic-array return prefix to every dynamic ABI type.
theorem decodeReturnSolc08Dynamic_eq {ty : ABIType} {out : ByteArray}
    (table : List (Nat × List CalldataPlan)) (hd : isDynamicABIType ty = true)
    (hs : out.size < 2^255) :
    decodeReturnValueWithMode? (.solc08Calldata table) ty out =
      if out.size < 32 then none else
      if solcMaxU64 < (calldataWord out 0).toNat then none else
        decodeValue? ty out.toList (calldataWord out 0).toNat {} := by
  have hsize : out.size < UInt256.size := by change out.size < 2^256; omega
  have hhead : abiTupleHeadSize? [ty] = some 32 := by
    simp only [abiTupleHeadSize?, hd, if_true, bind, Option.bind]
  have hcheck : solcSLT out.size 32 = decide (out.size < 32) := by
    rw [solcSLT_smallLeft hs (by decide)]
    simp only [show (32 : Nat) < 2^255 by decide, and_true]
  rw [decodeReturnValueWithMode?]
  simp only [decodeReturns?, hhead, List.isEmpty_cons, Bool.not_false, Bool.true_and, hcheck, bind, Option.bind]
  by_cases hh : out.size < 32
  · simp only [hh, decide_true, if_true]
  · simp only [hh, decide_false, Bool.false_eq_true, if_false, decodeFields?, stride?, hd,
      if_true, List.headD_nil, List.tail_nil, retainFailure, List.contains_nil, Bool.not_true,
      Bool.false_and, Bool.true_and, solcTailTarget?, bind, Option.bind,
      show solcAdd 0 0 = 0 from rfl, solcReadNat_word (by omega : 0+32 ≤ out.size) hsize]
    have ho : solcAdd 0 (calldataWord out 0).toNat = (calldataWord out 0).toNat := by
      simp only [solcAdd, Nat.zero_add]
      exact Nat.mod_eq_of_lt (calldataWord out 0).val.isLt
    rw [ho]
    by_cases hc : solcMaxU64 < (calldataWord out 0).toNat
    · simp only [hc, if_true, Option.bind_none]
    · simp only [hc, if_false, Option.bind_some]
      cases decodeValue? ty out.toList (calldataWord out 0).toNat {} <;> rfl

def schemaReturnOffset (out : ByteArray) : Nat := (calldataWord out 0).toNat
def schemaReturnValid (out : ByteArray) : Prop :=
  32 ≤ out.size ∧ schemaReturnOffset out ≤ solcMaxU64 ∧ schemaBodyValid out (schemaReturnOffset out)
instance (out : ByteArray) : Decidable (schemaReturnValid out) := by unfold schemaReturnValid; infer_instance

theorem decodeSchemaReturn {out : ByteArray} (hs : out.size < 2^255) :
    config.externalABI.decodeValue? schemaRecordABI out =
      if schemaReturnValid out then some (decodedSchemaRecord out (schemaReturnOffset out)).tuple else none := by
  change decodeReturnValueWithMode? (.solc08Calldata easPlanTable) schemaRecordABI out = _
  rw [decodeReturnSolc08Dynamic_eq easPlanTable (by native_decide) hs]
  by_cases hh : 32 ≤ out.size
  · rw [if_neg (by omega : ¬ out.size < 32)]
    by_cases ho : schemaReturnOffset out ≤ solcMaxU64
    · rw [if_neg (by change ¬ solcMaxU64 < schemaReturnOffset out; omega)]
      change decodeValue? schemaRecordABI out.toList (schemaReturnOffset out) {} = _
      rw [decodeSchemaBody ho hs]
      simp only [schemaReturnValid, hh, ho, true_and]
    · rw [if_pos (by change solcMaxU64 < schemaReturnOffset out; omega)]
      simp only [schemaReturnValid, ho, false_and, and_false, if_false]
  · rw [if_pos (by omega : out.size < 32)]
    simp only [schemaReturnValid, hh, false_and, if_false]

end Benchmarks.EAS.EAS
