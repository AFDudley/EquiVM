import Benchmarks.EAS.EAS.CopyRequestArrayStep
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def requestArrayElementValid (cd : ByteArray) (offset : UInt256) (i : Nat) : Prop :=
  (calldataWord cd (offset.toNat+32*i)).toNat ≤ 2^64-1 ∧ requestDataValid cd (requestArrayElement cd offset i)
instance (cd : ByteArray) (offset : UInt256) (i : Nat) : Decidable (requestArrayElementValid cd offset i) :=
  inferInstanceAs (Decidable (_ ∧ _))

def decodeRequestElements (cd : ByteArray) (offset : UInt256) (i : Nat) : Nat → Option (List AttestationRequestRecord)
  | 0 => some []
  | n+1 => if requestArrayElementValid cd offset i then
      (decodeRequestElements cd offset (i+1) n).map (requestDataRecord cd (requestArrayElement cd offset i) :: ·)
    else none

theorem requestArrayElement_decode (cd : ByteArray) (offset : UInt256) (i : Nat)
    (hb : offset.toNat+32*i < UInt256.size) :
    (do
      let target ← solcTailTarget? false requestDataABI cd.toList offset.toNat (solcAdd offset.toNat (32*i))
      decodeValue? requestDataABI cd.toList target {} false) =
      if requestArrayElementValid cd offset i then some (requestDataRecord cd (requestArrayElement cd offset i)).tuple else none := by
  have hslot : solcAdd offset.toNat (32*i) = (UInt256.ofNat (offset.toNat+32*i)).toNat := by
    rw [ulit_toNat' _ hb]
    exact Nat.mod_eq_of_lt hb
  have hread : solcReadNat cd.toList (solcAdd offset.toNat (32*i)) = (calldataWord cd (offset.toNat+32*i)).toNat := by
    rw [hslot,solcReadNat_word_total,ulit_toNat' _ hb]
  simp only [solcTailTarget?,hread,Bool.false_eq_true,if_false,bind,Option.bind_some]
  by_cases ho : (calldataWord cd (offset.toNat+32*i)).toNat ≤ 2^64-1
  · rw [if_neg (by change ¬ 18446744073709551615 < _; omega)]
    simp only [Option.bind_some]
    rw [solcAdd_word]
    change decodeValue? requestDataABI cd.toList (requestArrayElement cd offset i).toNat {} false = _
    rw [requestData_decode]
    by_cases hd : requestDataValid cd (requestArrayElement cd offset i)
    · rw [if_pos hd,if_pos ⟨ho,hd⟩]
    · rw [if_neg hd,if_neg (fun h => hd h.2)]
  · rw [if_pos (by change 18446744073709551615 < _; omega),if_neg (fun h => ho h.1)]
    rfl

theorem requestArrayElements_decode (cd : ByteArray) (offset : UInt256) (i n : Nat)
    (hb : offset.toNat+32*(i+n) < UInt256.size) :
    decodeElements? requestDataABI n cd.toList offset.toNat (32*i) {} true =
      (decodeRequestElements cd offset i n).map (List.map AttestationRequestRecord.tuple) := by
  induction n generalizing i with
  | zero => simp only [decodeElements?,decodeRequestElements,Option.map_some,List.map_nil]
  | succ n ih =>
    have hhead := requestArrayElement_decode cd offset i (by omega)
    simp only [bind] at hhead
    rw [decodeElements?]
    simp only [show isMemory ({} : CalldataPlan) = true from rfl,
      show isDynamicABIType requestDataABI = true by native_decide,
      show stride? requestDataABI = some 32 by native_decide,
      show child ({} : CalldataPlan) .element = ({} : CalldataPlan) from rfl,
      show (requestDataABI == .elem .bool) = false from rfl,
      Bool.not_true,Bool.and_false,Bool.false_eq_true,if_true,if_false,retainFailure,List.contains_nil,
      bind,Option.bind_some]
    rw [hhead,show 32*i+32 = 32*(i+1) by omega,ih (i+1) (by omega)]
    rw [decodeRequestElements]
    by_cases hv : requestArrayElementValid cd offset i
    · rw [if_pos hv,if_pos hv]
      cases decodeRequestElements cd offset (i+1) n <;> rfl
    · rw [if_neg hv,if_neg hv]
      rfl

theorem decodeRequestElements_facts {cd : ByteArray} {offset : UInt256} {i n : Nat} {rs : List AttestationRequestRecord}
    (h : decodeRequestElements cd offset i n = some rs) :
    rs.length = n ∧ ∀ j (hj : j < rs.length),
      requestArrayElementValid cd offset (i+j) ∧ requestDataRecord cd (requestArrayElement cd offset (i+j)) = rs[j] := by
  induction n generalizing i rs with
  | zero =>
    simp only [decodeRequestElements,Option.some.injEq] at h
    subst rs
    exact ⟨rfl,by intros; contradiction⟩
  | succ n ih =>
    rw [decodeRequestElements] at h
    by_cases hv : requestArrayElementValid cd offset i
    · rw [if_pos hv] at h
      cases ht : decodeRequestElements cd offset (i+1) n with
      | none => rw [ht] at h; contradiction
      | some tail =>
        rw [ht,Option.map_some,Option.some.injEq] at h
        subst rs
        obtain ⟨hlen,hvalues⟩ := ih ht
        refine ⟨by simp only [List.length_cons,hlen],?_⟩
        intro j hj
        cases j with
        | zero =>
          simp only [Nat.add_zero,List.getElem_cons_zero]
          exact ⟨hv,trivial⟩
        | succ j =>
          simpa only [List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm 1 j] using hvalues j (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hj)
    · rw [if_neg hv] at h
      contradiction

end Benchmarks.EAS.EAS
