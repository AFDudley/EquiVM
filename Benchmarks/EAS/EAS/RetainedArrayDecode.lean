import Benchmarks.EAS.EAS.DelegatedBatchDecode
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: a deferred element retains its decoding failure as a value.
def retainedArrayElement (ty : ABIType) (plan : CalldataPlan) (bytes : List UInt8)
    (base stride i : Nat) : Value :=
  (do
    let target ← if isDynamicABIType ty then
      solcTailTarget? (!isMemory plan) ty bytes base (solcAdd base (stride*i))
      else some (solcAdd base (stride*i))
    decodeValue? ty bytes target (child plan .element) (isDynamicABIType ty && !isMemory plan)).getD decodeFailure

def retainedArrayValues (ty : ABIType) (plan : CalldataPlan) (bytes : List UInt8)
    (base stride n : Nat) : List Value := (List.range n).map (retainedArrayElement ty plan bytes base stride)

theorem decodeRetainedElements {ty : ABIType} {plan : CalldataPlan} {stride : Nat}
    (hs : stride? ty=some stride) (hn : (ty == .elem .bool)=false)
    (hf : (child plan .element).deferErrors.contains []=true)
    (bytes : List UInt8) (base i n : Nat) (rawBools : Bool) :
    decodeElements? ty n bytes base (stride*i) plan rawBools =
      some ((List.range' i n).map (retainedArrayElement ty plan bytes base stride)) := by
  induction n generalizing i with
  | zero => simp only [decodeElements?,List.range'_zero,List.map_nil]
  | succ n ih =>
    rw [decodeElements?]
    simp only [hs,hn,Bool.and_false,Bool.false_eq_true,if_false,retainFailure,hf,if_true,
      bind,Option.bind_some]
    rw [show stride*i+stride=stride*(i+1) by rw [Nat.mul_add,Nat.mul_one],ih (i+1)]
    simp only [Option.bind_some,List.range'_succ,List.map_cons,retainedArrayElement]
    cases isDynamicABIType ty <;> rfl

def referencedArrayHeadValid (cd : ByteArray) (header : UInt256) (stride : Nat) : Prop :=
  (calldataWord cd header.toNat).toNat ≤ 2^64-1 ∧
  UInt256.slt (UInt256.ofNat cd.size-UInt256.ofNat ((calldataWord cd header.toNat).toNat*stride))
    (header+UInt256.ofNat 32) = ⟨0⟩
instance (cd : ByteArray) (header : UInt256) (stride : Nat) : Decidable (referencedArrayHeadValid cd header stride) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem referencedRetainedArray_decode {ty : ABIType} {plan : CalldataPlan} {stride : Nat}
    (hs : stride? ty=some stride) (hn : (ty == .elem .bool)=false)
    (hm : isMemory plan=false) (hf : (child plan .element).deferErrors.contains []=true)
    (cd : ByteArray) (header : UInt256) :
    decodeValue? (.dynamicArray ty) cd.toList header.toNat plan true =
      if referencedArrayHeadValid cd header stride then
        some (.array (retainedArrayValues ty plan cd.toList (header+UInt256.ofNat 32).toNat stride
          (calldataWord cd header.toNat).toNat)) else none := by
  have hlen : cd.toList.length=cd.size := by rw [byteArray_toList_eq,Array.length_toList]; rfl
  have hc : (child plan .element).deferErrors.isEmpty=false := by
    cases h : (child plan .element).deferErrors with
    | nil => rw [h] at hf; cases hf
    | cons a rest => rfl
  have hadd : solcAdd header.toNat 32=(header+UInt256.ofNat 32).toNat := solcAdd_word header (UInt256.ofNat 32)
  have hsub : solcSub cd.size ((calldataWord cd header.toNat).toNat*stride) =
      (UInt256.ofNat cd.size-UInt256.ofNat ((calldataWord cd header.toNat).toNat*stride)).toNat := rfl
  rw [decodeValue?]
  simp only [solcReadNat_word_total,hs,hm,hc,Bool.and_false,Bool.false_eq_true,if_false,
    badExtent,Bool.not_true,Bool.false_and,Bool.not_false,Bool.true_and,Bool.false_or,
    bind,Option.bind_some,hlen,hadd,hsub,Bool.true_eq,if_true]
  by_cases hl : (calldataWord cd header.toNat).toNat ≤ 2^64-1
  · have hl' : ¬solcMaxU64 < (calldataWord cd header.toNat).toNat := by change ¬18446744073709551615<_ ; omega
    simp only [hl',decide_false,Bool.false_or]
    by_cases he : UInt256.slt (UInt256.ofNat cd.size-UInt256.ofNat ((calldataWord cd header.toNat).toNat*stride))
        (header+UInt256.ofNat 32) = ⟨0⟩
    · rw [(solcSLT_word_false _ _).mpr he,if_pos (show referencedArrayHeadValid cd header stride from ⟨hl,he⟩)]
      simp only [Bool.false_eq_true,if_false]
      have hd := decodeRetainedElements hs hn hf cd.toList (header+UInt256.ofNat 32).toNat 0
        (calldataWord cd header.toNat).toNat true
      simp only [Nat.mul_zero,Nat.zero_add,← List.range_eq_range'] at hd
      rw [hd]
      rfl
    · have he' : solcSLT (UInt256.ofNat cd.size-UInt256.ofNat ((calldataWord cd header.toNat).toNat*stride)).toNat
          (header+UInt256.ofNat 32).toNat=true := by
        cases h : solcSLT (UInt256.ofNat cd.size-UInt256.ofNat ((calldataWord cd header.toNat).toNat*stride)).toNat
            (header+UInt256.ofNat 32).toNat
        · exact False.elim (he ((solcSLT_word_false _ _).mp h))
        · rfl
      rw [he',if_neg (fun (h : referencedArrayHeadValid cd header stride) => he h.2)]
      rfl
  · have hl' : solcMaxU64 < (calldataWord cd header.toNat).toNat := by change 18446744073709551615<_ ; omega
    rw [if_neg (fun (h : referencedArrayHeadValid cd header stride) => hl h.1)]
    simp only [hl',decide_true,Bool.true_or,if_true]

end Benchmarks.EAS.EAS
