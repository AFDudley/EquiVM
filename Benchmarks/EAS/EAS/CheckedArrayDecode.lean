import Benchmarks.EAS.EAS.StaticArrayDecode
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: a static array succeeds exactly when every element's local check succeeds.
theorem decodeStaticArray_of_checked_elements {α : Type} (value : α → Value) (valid : α → Prop)
    [DecidablePred valid] {ty : ABIType} {bytes : List UInt8} {start stride : Nat} {xs : List α}
    (h : ∀ i (hi : i<xs.length), decodeABIValue? ty bytes (start+stride*i) =
      if valid xs[i] then some (value xs[i],start+stride*(i+1)) else none) :
    decodeABIArrayStaticElems? ty xs.length stride bytes start =
      if ∀ x∈xs,valid x then some (xs.map value,start+stride*xs.length) else none := by
  induction xs generalizing start with
  | nil =>
    rw [if_pos (by intro x hx; cases hx)]
    simp only [List.length_nil,decodeABIArrayStaticElems?,Nat.mul_zero,Nat.add_zero,List.map_nil,List.not_mem_nil,false_implies,forall_const,if_true]
  | cons a rest ih =>
    have h0 := h 0 (by simp)
    simp only [Nat.mul_zero,Nat.add_zero,Nat.zero_add,Nat.mul_one,List.getElem_cons_zero] at h0
    rw [List.length_cons,decodeABIArrayStaticElems?,h0]
    by_cases ha : valid a
    · rw [if_pos ha]
      simp only [bind,Option.bind_some,if_true]
      have ht : ∀ i (hi : i<rest.length), decodeABIValue? ty bytes (start+stride+stride*i) =
          if valid rest[i] then some (value rest[i],start+stride+stride*(i+1)) else none := by
        intro i hi
        simpa only [List.getElem_cons_succ,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm stride] using
          h (i+1) (by simp only [List.length_cons]; omega)
      rw [ih ht]
      by_cases hr : ∀ x∈rest,valid x
      · rw [if_pos hr,if_pos (List.forall_mem_cons.mpr ⟨ha,hr⟩)]
        simp only [Option.bind_some,pure,List.map_cons,
          Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm stride]
      · simp only [if_neg hr,List.forall_mem_cons,ha,hr,and_false,if_false,Option.bind_none]
    · simp only [if_neg ha,bind,Option.bind_none,List.forall_mem_cons,ha,false_and,if_false]

end Benchmarks.EAS.EAS
