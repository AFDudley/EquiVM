import Benchmarks.EAS.EAS.ArrayCalldataBounds
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: lazy outer-array decoding depends only on the element stride and reference policy.
theorem referencedArray_decode_eq {ty : ABIType} {plan : CalldataPlan}
    (hd : isDynamicABIType ty = true) (hm : isMemory plan = false) (cd : ByteArray) (start : Nat) :
    decodeValue? (.dynamicArray ty) cd.toList start plan false =
      if solcMaxU64 < solcReadNat cd.toList start || badExtent true false cd.toList start (solcReadNat cd.toList start) 32 then none else
        (decodeElements? ty (solcReadNat cd.toList start) cd.toList
          (solcAdd start 32) 0 plan true).map Value.array := by
  rw [decodeValue?]
  simp only [show stride? ty = some 32 by simp only [stride?,hd,if_true],
    hm,
    hd,
    Bool.not_true,Bool.false_and,Bool.false_eq_true,if_false,bind,Option.bind_some,
    show badExtent false false cd.toList start (solcReadNat cd.toList start) 32 =
      badExtent true false cd.toList start (solcReadNat cd.toList start) 32 from rfl]
  split
  · rfl
  · cases decodeElements? ty (solcReadNat cd.toList start) cd.toList
      (solcAdd start 32) 0 plan true <;> rfl

-- LIBRARY CANDIDATE: decode a single referenced array argument with an arbitrary element type and plan.
theorem decodeReferencedArray_eq {ty : ABIType} {plan : CalldataPlan}
    (hd : isDynamicABIType ty = true) (hm : isMemory plan = false)
    (hf : plan.deferErrors.contains [] = false) {cd : ByteArray} (name : Ident) (table : List (Nat × List CalldataPlan))
    (h4 : 4 ≤ cd.size) (hhead : solcSLT (solcSub cd.size 4) 32 = false)
    (hplans : ((table.find? (fun entry => entry.1 == (bytesToWord (cd.toList.take 4)).toNat)).map Prod.snd).getD [] = [plan]) :
    decodeCalldataWithMode (.solc08Calldata table) [name] [.dynamicArray ty] cd =
      if solcMaxU64 < solcReadNat cd.toList 4 then none else
        let start := solcAdd 4 (solcReadNat cd.toList 4)
        let size := solcReadNat cd.toList start
        if solcMaxU64 < size || badExtent true false cd.toList start size 32 then none else
          (decodeElements? ty size cd.toList (solcAdd start 32) 0 plan true).map
            (fun values => (∅ : Store).insert name (.array values)) := by
  rw [decodeCalldataSolc08,if_neg (by omega : ¬ cd.size < 4)]
  simp only [decodeArgs?,List.isEmpty_cons,Bool.false_eq_true,if_false,
    show abiTupleHeadSize? [.dynamicArray ty] = some 32 by
      simp only [abiTupleHeadSize?,isDynamicABIType,if_true,bind,Option.bind],
    bind,Option.bind,hhead,hplans]
  simp only [decodeFields?,show stride? (.dynamicArray ty) = some 32 from rfl,
    show isDynamicABIType (.dynamicArray ty) = true from rfl,
    if_true,if_false,List.headD_cons,List.tail_cons,retainFailure,
    hf,
    Bool.false_eq_true,solcTailTarget?,Bool.not_true,show solcAdd 4 0 = 4 from rfl,
    bind,Option.bind,Bool.true_and,Bool.and_false,pure]
  by_cases ho : solcMaxU64 < solcReadNat cd.toList 4
  · simp only [ho,if_true,Option.bind_none]
  · simp only [ho,if_false]
    rw [referencedArray_decode_eq hd hm]
    cases hb : (decide (solcMaxU64 < solcReadNat cd.toList (solcAdd 4 (solcReadNat cd.toList 4))) ||
        badExtent true false cd.toList (solcAdd 4 (solcReadNat cd.toList 4))
          (solcReadNat cd.toList (solcAdd 4 (solcReadNat cd.toList 4))) 32)
    · simp only [hb,Bool.false_eq_true,if_false]
      cases decodeElements? ty (solcReadNat cd.toList (solcAdd 4 (solcReadNat cd.toList 4))) cd.toList
        (solcAdd (solcAdd 4 (solcReadNat cd.toList 4)) 32) 0 plan true <;> rfl
    · rfl

-- LIBRARY CANDIDATE: isolate selector/head/extent checks from lazy element decoding.
theorem decodeReferencedArray {ty : ABIType} {plan : CalldataPlan}
    (hd : isDynamicABIType ty = true) (hm : isMemory plan = false)
    (hf : plan.deferErrors.contains [] = false) {cd : ByteArray}
    (name : Ident) (table : List (Nat × List CalldataPlan))
    (h36 : 36 ≤ cd.size) (hbig : cd.size < 2^255+4) (hsize : cd.size < UInt256.size)
    (hplans : ((table.find? (fun entry => entry.1 == (bytesToWord (cd.toList.take 4)).toNat)).map Prod.snd).getD [] = [plan]) :
    decodeCalldataWithMode (.solc08Calldata table) [name] [.dynamicArray ty] cd =
      if wordArrayValid cd then
        (decodeElements? ty (wordArrayLength cd) cd.toList (wordArrayOffset cd+36) 0 plan true).map
          (fun values => (∅ : Store).insert name (.array values)) else none := by
  rw [decodeReferencedArray_eq hd hm hf name table (by omega)
    (solcSLT_sub4_of_check (need := ⟨32⟩) (bit := false) (solcDecodeLenCheckOk_4_32 h36 hbig hsize)) hplans,
    solcReadNat_word h36 hsize]
  exact wordArrayGuards (fun start n => (decodeElements? ty n cd.toList start 0 plan true).map
    (fun values => (∅ : Store).insert name (.array values))) hsize

-- LIBRARY CANDIDATE: compose retained element decodes without unfolding the element type.
theorem decodeReferencedElements {ty : ABIType} {plan : CalldataPlan}
    (hd : isDynamicABIType ty = true) (hm : isMemory plan = false)
    (hn : (ty == .elem .bool) = false) (bytes : List UInt8) (base i n : Nat) (value : Nat → Value)
    (h : ∀ j, i ≤ j → j < i+n → retainFailure (child plan .element) (do
      let target ← solcTailTarget? true ty bytes base (solcAdd base (32*j))
      decodeValue? ty bytes target (child plan .element) true) = some (value j)) :
    decodeElements? ty n bytes base (32*i) plan true = some ((List.range' i n).map value) := by
  induction n generalizing i with
  | zero => simp only [decodeElements?,List.range'_zero,List.map_nil]
  | succ n ih =>
    have hhead := h i (by omega) (by omega)
    simp only [bind] at hhead
    rw [decodeElements?]
    simp only [hm,hd,show stride? ty = some 32 by simp only [stride?,hd,if_true],hn,
      Bool.not_false,Bool.and_false,Bool.false_eq_true,if_true,if_false,Bool.true_and,
      bind,Option.bind_some]
    rw [hhead,show 32*i+32 = 32*(i+1) by omega,ih (i+1) (by
      intro j hlo hhi
      exact h j (by omega) (by omega))]
    simp only [Option.bind_some,List.range'_succ,List.map_cons]

end Benchmarks.EAS.EAS
