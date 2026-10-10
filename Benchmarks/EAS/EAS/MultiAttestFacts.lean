import Benchmarks.EAS.EAS.MultiAttestControl
import Benchmarks.EAS.EAS.MultiAttestRead
import Benchmarks.EAS.EAS.MergeUIDRun
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

theorem multiRequestValues_length (cd : ByteArray) (base : UInt256) (n : Nat) :
    (multiRequestValues cd base n).length = n := by simp only [multiRequestValues,List.length_map,List.length_range]

theorem multiRequestValues_get (cd : ByteArray) (base : UInt256) (n i : Nat)
    (hi : i < (multiRequestValues cd base n).length) :
    (multiRequestValues cd base n)[i] = multiRequestValue cd base i := by
  simp only [multiRequestValues,List.getElem_map,List.getElem_range]

theorem multiRequestValue_normalizes (cd : ByteArray) (base : UInt256) (i : Nat) :
    normalizeRawBoolWord? (multiRequestValue cd base i) = .ok (multiRequestValue cd base i) := by
  unfold multiRequestValue
  cases decodeMultiRequest cd base i <;> rfl

theorem multiAttestLastWord_eq {n i : Nat} (hi : i<n) (hn : n<UInt256.size) :
    multiAttestLastWord n i = (decide (i=n-1)).toUInt256 := by
  have hs : UInt256.ofNat n-⟨1⟩ = UInt256.ofNat (n-1) := by
    simpa only [ulit_toNat' _ hn] using u256_sub_one_eq_pred_of_pos (UInt256.ofNat n)
      (by rw [ulit_toNat' _ hn]; omega)
  have he : UInt256.ofNat i = UInt256.ofNat (n-1) ↔ i=n-1 := by
    constructor
    · intro h
      have hh := congrArg UInt256.toNat h
      simpa only [ulit_toNat' _ (by omega : i<UInt256.size),ulit_toNat' _ (by omega : n-1<UInt256.size)] using hh
    · intro h; rw [h]
  simp only [multiAttestLastWord,hs,UInt256.eq,UInt256.fromBool,he]

-- LIBRARY CANDIDATE: the unused suffix of an incrementally filled array table.
def EmptyArraySuffix {α : Type} (groups : List (List α)) (filled : Nat) : Prop :=
  ∀ j (hj : j<groups.length), filled≤j → groups[j]=[]

theorem EmptyArraySuffix.replicate {α : Type} (n : Nat) :
    EmptyArraySuffix (List.replicate n ([] : List α)) 0 := by
  intro j hj _
  exact List.getElem_replicate hj

theorem EmptyArraySuffix.set {α : Type} {groups : List (List α)} {i : Nat}
    (h : EmptyArraySuffix groups i) (words : List α) : EmptyArraySuffix (groups.set i words) (i+1) := by
  intro j hj hle
  rw [List.getElem_set_ne (by omega : i≠j)]
  exact h j (by simpa only [List.length_set] using hj) (by omega)

-- LIBRARY CANDIDATE: replacing an empty component adds precisely its new length.
theorem flattenLength_set_empty {α : Type} (groups : List (List α)) (words : List α) (i : Nat)
    (hi : i<groups.length) (he : groups[i]=[]) :
    (groups.set i words).flatten.length = groups.flatten.length+words.length := by
  induction groups generalizing i with
  | nil => simp only [List.length_nil] at hi; omega
  | cons xs rest ih =>
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero] at he
      simp only [List.set_cons_zero,List.flatten_cons,List.length_append,he,List.length_nil]
      omega
    | succ i =>
      have h := ih i (by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hi) he
      simp only [List.set_cons_succ,List.flatten_cons,List.length_append]
      omega

end Benchmarks.EAS.EAS
