import Benchmarks.Morpho.MetaMorphoV1_1.BytesArrayCalldata
import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayCalldata

/-! The bytes-array decoder has the same outer checks as the compiler's word-array view. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach ABI.Solc08Calldata
open Benchmarks.EAS.Attester (ArrayHeadChecks)

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false
set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: normalize the ABI array end after its uint64 length guard.
theorem solcArrayEnd_word (head len : UInt256) (hl : len.toNat ≤ solcMaxU64) :
    solcAdd (solcAdd head.toNat 32) (len.toNat * 32) =
      (head + UInt256.shiftLeft len (UInt256.ofNat 5) + UInt256.ofNat 32).toNat := by
  have hb : 32 * len.toNat < UInt256.size := by
    change len.toNat ≤ 18446744073709551615 at hl
    change _ < 2 ^ 256
    omega
  have hshift : UInt256.shiftLeft len (UInt256.ofNat 5) =
      UInt256.ofNat (32 * len.toNat) := by
    conv_lhs => rw [← u256_ofNat_toNat len]
    exact shiftLeft5_ofNat_eq hb
  have h32 : solcAdd head.toNat 32 = (head + UInt256.ofNat 32).toNat :=
    solcAdd_word head (UInt256.ofNat 32)
  rw [hshift, h32, Nat.mul_comm len.toNat 32,
    ← UInt256.toNat_ofNat_of_lt hb, solcAdd_word, u256_ofNat_toNat]
  rw [u256_add_assoc, u256_add_comm (UInt256.ofNat 32), ← u256_add_assoc]

open Classical in
set_option maxHeartbeats 600000 in
theorem decodeCalldataBytesArrayHead (cd : ByteArray) (head : UInt256) :
    decodeValue? (.dynamicArray .bytes) cd.toList head.toNat multicallCalldataPlan false =
      if ArrayHeadChecks cd head then some (.array (calldataBytesArrayValues cd head))
      else none := by
  classical
  rw [decodeCalldataBytesArrayValue]
  by_cases hl : (calldataWord cd head.toNat).toNat ≤ solcMaxU64
  case neg =>
    have hn : solcMaxU64 < (calldataWord cd head.toNat).toNat := by omega
    rw [if_neg (fun (hc : ArrayHeadChecks cd head) ↦ hl (uint64Bound_of_isZero_gt hc.length))]
    simp only [hn, decide_true, Bool.true_or, if_true]
  have hlw : UInt256.isZero (UInt256.gt (calldataWord cd head.toNat)
      (UInt256.ofNat 18446744073709551615)) ≠ UInt256.ofNat 0 := by
    rw [ugt_zero hl]
    decide
  have h31 : solcAdd head.toNat 31 = (head + UInt256.ofNat 31).toNat :=
    solcAdd_word head (UInt256.ofNat 31)
  have hsl : solcSLT (solcAdd head.toNat 31) cd.size =
      solcSLT (head + UInt256.ofNat 31).toNat (UInt256.ofNat cd.size).toNat := by
    rw [h31]
    unfold solcSLT EVM.Word.ofNat
    simp only [u256_ofNat_toNat]
  have hsize : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  simp only [show ¬ solcMaxU64 < (calldataWord cd head.toNat).toNat by omega,
    decide_false, Bool.false_or, badExtent, Bool.not_false, Bool.true_and,
    Bool.false_and, Bool.false_eq_true, if_false, hsize, hsl, solcArrayEnd_word head _ hl]
  change (if (!solcSLT (head + UInt256.ofNat 31).toNat (UInt256.ofNat cd.size).toNat ||
      decide ((UInt256.ofNat cd.size).toNat <
        (head + UInt256.shiftLeft (calldataWord cd head.toNat) (UInt256.ofNat 5) +
          UInt256.ofNat 32).toNat)) = true then none else _) = _
  by_cases hh : UInt256.slt (head + UInt256.ofNat 31) (UInt256.ofNat cd.size) = ⟨0⟩
  · rw [(solcSLT_word_false _ _).mpr hh]
    simp only [Bool.not_false, Bool.true_or, if_true]
    rw [if_neg (fun (hc : ArrayHeadChecks cd head) ↦ hc.header hh)]
  · have hs : solcSLT (head + UInt256.ofNat 31).toNat
        (UInt256.ofNat cd.size).toNat = true := by
      cases he : solcSLT (head + UInt256.ofNat 31).toNat (UInt256.ofNat cd.size).toNat
      · exact False.elim (hh ((solcSLT_word_false _ _).mp he))
      · rfl
    rw [hs]
    simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq]
    by_cases he : (head + UInt256.shiftLeft (calldataWord cd head.toNat) (UInt256.ofNat 5) +
        UInt256.ofNat 32).toNat ≤ (UInt256.ofNat cd.size).toNat
    · have hc : ArrayHeadChecks cd head := ⟨hh, hlw, by rw [ugt_zero he]; decide⟩
      rw [if_neg (by omega), if_pos hc]
    · rw [if_pos (by omega), if_neg (fun (hc : ArrayHeadChecks cd head) ↦
        he (ugt_eq_zero_to_le (u256_isZero_ne_zero_to_eq_zero hc.payload)))]

end Benchmarks.Morpho.MetaMorphoV1_1
