import Reasoning.ABIViews

/-! Generic word and retained-element facts for the calldata-reference ABI API.

These are library candidates. The proof patterns also occur in EAS's calldata modules;
keeping their dependencies local avoids importing that benchmark's contract and runtime.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false
set_option maxRecDepth 2000

-- GENERALIZES Reasoning.Theory.readBytes32_toList to arbitrary addresses and lengths.
theorem readBytes_padded_toList (cd : ByteArray) (start size : Nat) :
    (cd.readBytes start size).toList =
      (cd.toList.drop start).take size ++
        List.replicate (size - ((cd.toList.drop start).take size).length) 0 := by
  unfold ByteArray.readBytes
  split
  · have hc : (cd.copySlice start ByteArray.empty 0 size).toList =
        (cd.toList.drop start).take size := by
      have h : (cd.copySlice start ByteArray.empty 0 size).data =
          cd.data.extract start (start + size) := by
        rw [ByteArray.data_copySlice]
        simp
      rw [byteArray_toList_eq, h, Array.toList_extract, List.extract_eq_take_drop,
        Nat.add_sub_cancel_left, byteArray_toList_eq]
    have hs : (cd.copySlice start ByteArray.empty 0 size).size =
        ((cd.toList.drop start).take size).length := by
      rw [← hc, byteArray_toList_eq, Array.length_toList]
      rfl
    rw [byteArray_toList_eq (_ ++ _), ByteArray.data_append, Array.toList_append,
      ← byteArray_toList_eq, hc, byteArray_zeroes_toList, hs]
  · simp only [byteArray_toList_eq, ByteArray.data_append, Array.toList_append,
      ByteArray.size, List.size_toArray, byteArray_zeroes_toList]

-- LIBRARY CANDIDATE: identify the new ABI reader with CALLDATALOAD at every word address.
theorem solcReadNat_word_total (cd : ByteArray) (start : UInt256) :
    solcReadNat cd.toList start.toNat = (calldataWord cd start.toNat).toNat := by
  have he : solcReadBytes cd.toList start.toNat 32 = (cd.readBytes start.toNat 32).toList := by
    rw [readBytes_padded_toList]
    simp only [solcReadBytes, Nat.mod_eq_of_lt
      (show start.toNat < EVM.wordModulus from start.val.isLt)]
  unfold solcReadNat
  rw [he]
  change (bytesToWord _).toNat = (uInt256OfByteArray _).toNat
  rw [uInt256OfByteArray_eq]
  unfold bytesToWord fromByteArrayBigEndian
  congr 3
  simp only [byteArray_toList_eq]

-- LIBRARY CANDIDATE: the ABI wrapping arithmetic agrees with word operations.
theorem solcAdd_word (a b : UInt256) : solcAdd a.toNat b.toNat = (a + b).toNat :=
  (uadd_toNat a b).symm

theorem solcSub_word (a b : UInt256) : solcSub a.toNat b.toNat = (a - b).toNat := by
  unfold solcSub EVM.Word.ofNat
  rw [u256_ofNat_toNat, u256_ofNat_toNat]

theorem solcSLT_word (a b : UInt256) :
    solcSLT a.toNat b.toNat = UInt256.sltBool a b := by
  unfold solcSLT EVM.Word.ofNat
  rw [u256_ofNat_toNat, u256_ofNat_toNat]
  have haBound : a.toNat < 2 ^ 256 := a.val.isLt
  have hbBound : b.toNat < 2 ^ 256 := b.val.isLt
  change decide
      ((if a.toNat < 2 ^ 255 then (a.toNat : Int) else (a.toNat : Int) - 2 ^ 256) <
       (if b.toNat < 2 ^ 255 then (b.toNat : Int) else (b.toNat : Int) - 2 ^ 256)) =
    (if 2 ^ 255 ≤ a.toNat then
      (if 2 ^ 255 ≤ b.toNat then decide (a.toNat < b.toNat) else true)
    else (if 2 ^ 255 ≤ b.toNat then false else decide (a.toNat < b.toNat)))
  by_cases ha : a.toNat < 2 ^ 255 <;> by_cases hb : b.toNat < 2 ^ 255
  · simp only [ha, hb, not_le_of_gt ha, not_le_of_gt hb, if_pos, if_false]
    congr 1
    apply propext
    omega
  · simp only [ha, hb, not_le_of_gt ha, Nat.le_of_not_gt hb, if_pos, if_false]
    exact decide_eq_false (by omega)
  · simp only [ha, hb, Nat.le_of_not_gt ha, not_le_of_gt hb, if_pos, if_false]
    exact decide_eq_true (by omega)
  · simp only [ha, hb, Nat.le_of_not_gt ha, Nat.le_of_not_gt hb, if_pos, if_false]
    congr 1
    apply propext
    omega

theorem solcSLT_word_false (a b : UInt256) :
    solcSLT a.toNat b.toNat = false ↔ UInt256.slt a b = ⟨0⟩ := by
  rw [solcSLT_word]
  unfold UInt256.slt
  cases UInt256.sltBool a b <;> decide

def retainedCalldataElement (ty : ABIType) (plan : CalldataPlan) (bytes : List UInt8)
    (base stride i : Nat) : Value :=
  (do
    let target ← if isDynamicABIType ty then
      solcTailTarget? (!isMemory plan) ty bytes base (solcAdd base (stride * i))
      else some (solcAdd base (stride * i))
    decodeValue? ty bytes target (child plan .element)
      (isDynamicABIType ty && !isMemory plan)).getD decodeFailure

-- LIBRARY CANDIDATE: each retained failure is a value at its original array index.
theorem decodeRetainedCalldataElements {ty : ABIType} {plan : CalldataPlan} {stride : Nat}
    (hs : stride? ty = some stride) (hn : (ty == .elem .bool) = false)
    (hf : (child plan .element).deferErrors.contains [] = true)
    (bytes : List UInt8) (base i n : Nat) (rawBools : Bool) :
    decodeElements? ty n bytes base (stride * i) plan rawBools =
      some ((List.range' i n).map (retainedCalldataElement ty plan bytes base stride)) := by
  induction n generalizing i with
  | zero => simp only [decodeElements?, List.range'_zero, List.map_nil]
  | succ n ih =>
    rw [decodeElements?]
    simp only [hs, hn, Bool.and_false, Bool.false_eq_true, if_false,
      retainFailure, hf, if_true, bind, Option.bind_some]
    rw [show stride * i + stride = stride * (i + 1) by rw [Nat.mul_add, Nat.mul_one], ih]
    simp only [Option.bind_some, List.range'_succ, List.map_cons, retainedCalldataElement]
    cases isDynamicABIType ty <;> rfl

-- LIBRARY CANDIDATE: expose only this decoder mode's entry checks.
theorem decodeCalldataSolc08 (table : List (Nat × List CalldataPlan))
    (names : List Ident) (types : List ABIType) (cd : ByteArray) :
    decodeCalldataWithMode (.solc08Calldata table) names types cd =
      if cd.size < 4 then none else
        (decodeArgs? table types cd).bind (fun vs ↦ decodeCalldata.insertValues names vs ∅) := by
  have hl : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  simp only [decodeCalldataWithMode, decodeCalldata, hl]
  split
  · rfl
  · split <;> rfl

end Benchmarks.Morpho.MetaMorphoV1_1
