import Benchmarks.EAS.EAS.CalldataPlans
import Benchmarks.EAS.EAS.WordArrayBase
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
open ABI.Solc08Calldata
set_option maxRecDepth 10000

def wordArrayOffset (cd : ByteArray) : Nat := (calldataWord cd 4).toNat
def wordArrayLength (cd : ByteArray) : Nat := (calldataWord cd (4 + wordArrayOffset cd)).toNat
def wordArrayValid (cd : ByteArray) : Prop :=
  wordArrayOffset cd ≤ solcMaxU64 ∧ cd.size < 2^255 ∧ wordArrayOffset cd + 36 ≤ cd.size ∧
    wordArrayLength cd ≤ solcMaxU64 ∧ wordArrayOffset cd + 36 + 32 * wordArrayLength cd ≤ cd.size
instance (cd : ByteArray) : Decidable (wordArrayValid cd) := by unfold wordArrayValid; infer_instance

-- LIBRARY CANDIDATE: the top-level word-stride array bounds do not depend on its elements.
theorem wordArrayGuards {α : Type} {cd : ByteArray} (payload : Nat → Nat → Option α)
    (hsize : cd.size < UInt256.size) :
    (if solcMaxU64 < wordArrayOffset cd then none else
      let start := solcAdd 4 (wordArrayOffset cd)
      let size := solcReadNat cd.toList start
      if solcMaxU64 < size || badExtent true false cd.toList start size 32 then none else
        payload (solcAdd start 32) size) =
      if wordArrayValid cd then payload (wordArrayOffset cd+36) (wordArrayLength cd) else none := by
  by_cases ho : wordArrayOffset cd ≤ solcMaxU64
  · rw [if_neg (by omega : ¬ solcMaxU64 < wordArrayOffset cd)]
    have hos : wordArrayOffset cd + 68 < 2^255 := by
      change wordArrayOffset cd ≤ 18446744073709551615 at ho
      omega
    have hstart : solcAdd 4 (wordArrayOffset cd) = 4 + wordArrayOffset cd :=
      Nat.mod_eq_of_lt (by change 4 + wordArrayOffset cd < 2^256; omega)
    have h31 : solcAdd (4 + wordArrayOffset cd) 31 = wordArrayOffset cd + 35 := by
      unfold solcAdd
      rw [Nat.mod_eq_of_lt (by change 4 + wordArrayOffset cd + 31 < 2^256; omega)]
      omega
    have h32 : solcAdd (4 + wordArrayOffset cd) 32 = wordArrayOffset cd + 36 := by
      unfold solcAdd
      rw [Nat.mod_eq_of_lt (by change 4 + wordArrayOffset cd + 32 < 2^256; omega)]
      omega
    have hlen : cd.toList.length = cd.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
    have hmod : cd.size % EVM.wordModulus = cd.size := Nat.mod_eq_of_lt hsize
    rw [hstart]
    dsimp only
    by_cases hh : cd.size < 2^255 ∧ wordArrayOffset cd + 36 ≤ cd.size
    · have hr : solcReadNat cd.toList (4 + wordArrayOffset cd) = wordArrayLength cd :=
        solcReadNat_word (by omega) hsize
      have hheader : solcSLT (solcAdd (4 + wordArrayOffset cd) 31) cd.size = true := by
        rw [h31, solcSLT_smallLeft (by omega) hsize]
        exact decide_eq_true (by omega)
      rw [hr, h32]
      simp only [badExtent, hlen, Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and,
        Bool.false_eq_true, if_false, hheader, Bool.false_or, hmod]
      by_cases hn : wordArrayLength cd ≤ solcMaxU64
      · have hnlarge : wordArrayLength cd ≤ 18446744073709551615 := hn
        have hlast : solcAdd (wordArrayOffset cd + 36) (wordArrayLength cd * 32) =
            wordArrayOffset cd + 36 + 32 * wordArrayLength cd := by
          unfold solcAdd
          rw [Nat.mod_eq_of_lt (by change wordArrayOffset cd + 36 + wordArrayLength cd * 32 < 2^256; omega)]
          omega
        rw [h32, hlast]
        by_cases hp : wordArrayOffset cd + 36 + 32 * wordArrayLength cd ≤ cd.size
        · simp only [show ¬ solcMaxU64 < wordArrayLength cd by omega,
            show ¬ cd.size < wordArrayOffset cd + 36 + 32 * wordArrayLength cd by omega,
            decide_false, Bool.false_or, Bool.false_eq_true, if_false]
          rw [if_pos (show wordArrayValid cd from ⟨ho, hh.1, hh.2, hn, hp⟩)]
        · simp only [show cd.size < wordArrayOffset cd + 36 + 32 * wordArrayLength cd by omega,
            decide_true, Bool.or_true, if_true]
          rw [if_neg (by intro h; exact hp h.2.2.2.2)]
      · simp only [show solcMaxU64 < wordArrayLength cd by omega, decide_true, Bool.true_or, if_true]
        rw [if_neg (by intro h; exact hn h.2.2.2.1)]
    · have hheader : solcSLT (solcAdd (4 + wordArrayOffset cd) 31) cd.size = false := by
        rw [h31, solcSLT_smallLeft (by omega) hsize]
        exact decide_eq_false (by omega)
      simp only [badExtent, hlen, Bool.not_false, Bool.true_and, hheader, Bool.true_or, Bool.or_true, if_true]
      rw [if_neg (by intro h; exact hh ⟨h.2.1, h.2.2.1⟩)]
  · rw [if_pos (by omega : solcMaxU64 < wordArrayOffset cd), if_neg (by intro h; exact ho h.1)]

end Benchmarks.EAS.EAS
