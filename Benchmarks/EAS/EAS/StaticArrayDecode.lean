import Benchmarks.EAS.EAS.RevokeDecode
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS

-- LIBRARY CANDIDATE: complete static ABI word reads form one contiguous slice.
theorem solcReadWords_slice {bytes : List UInt8} {start n : Nat}
    (hb : start+32*n ≤ bytes.length) (hcap : bytes.length < EVM.wordModulus) :
    solcReadWords bytes start n = (bytes.drop start).take (32*n) := by
  have aux (i k : Nat) (hk : start+32*(i+k) ≤ bytes.length) :
      (List.range' i k).flatMap (fun j => solcReadBytes bytes (solcAdd start (32*j)) 32) =
        (bytes.drop (start+32*i)).take (32*k) := by
    induction k generalizing i with
    | zero => simp only [List.range'_zero,List.flatMap_nil,Nat.mul_zero,List.take_zero]
    | succ k ih =>
      have hm : solcAdd start (32*i) = start+32*i := Nat.mod_eq_of_lt (by omega)
      have hl : ((bytes.drop (start+32*i)).take 32).length = 32 := by
        rw [List.length_take,List.length_drop]; omega
      rw [List.range'_succ,List.flatMap_cons,ih (i+1) (by omega)]
      simp only [solcReadBytes,hm,Nat.mod_eq_of_lt (by omega : start+32*i < EVM.wordModulus),hl,
        Nat.sub_self,List.replicate_zero,List.append_nil]
      rw [show 32*(k+1) = 32+32*k by omega,List.take_add,List.drop_drop]
      congr 2
  simpa only [solcReadWords,List.range_eq_range',Nat.zero_add,Nat.mul_zero,Nat.add_zero] using aux 0 n (by omega)

-- LIBRARY CANDIDATE: compose bounded static element decodes without unfolding their types.
theorem decodeStaticArray_of_elements {ty : ABIType} {bytes : List UInt8} {start stride : Nat} {values : List Value}
    (h : ∀ i (hi : i < values.length), decodeABIValue? ty bytes (start+stride*i) =
      some (values[i],start+stride*(i+1))) :
    decodeABIArrayStaticElems? ty values.length stride bytes start = some (values,start+stride*values.length) := by
  induction values generalizing start with
  | nil => simp only [List.length_nil,decodeABIArrayStaticElems?,Nat.mul_zero,Nat.add_zero]
  | cons a rest ih =>
    have h0 := h 0 (by simp)
    simp only [Nat.mul_zero,Nat.add_zero,Nat.zero_add,Nat.mul_one,List.getElem_cons_zero] at h0
    rw [List.length_cons,decodeABIArrayStaticElems?,h0]
    simp only [bind,Option.bind,if_true]
    have ht : ∀ i (hi : i < rest.length), decodeABIValue? ty bytes (start+stride+stride*i) =
        some (rest[i],start+stride+stride*(i+1)) := by
      intro i hi
      simpa only [List.getElem_cons_succ,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm stride] using h (i+1) (by simp only [List.length_cons]; omega)
    rw [ih ht]
    simp only [Option.bind_some,pure,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm stride]

end Benchmarks.EAS.EAS
