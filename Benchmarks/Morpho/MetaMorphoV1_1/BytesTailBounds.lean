import Benchmarks.Morpho.MetaMorphoV1_1.BytesArrayElement

/-! Accepted materialized byte tails satisfy the compiler's signed and copying guards. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory ABI.Solc08Calldata

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false
set_option maxRecDepth 2000

-- LIBRARY CANDIDATE: a valid materialized tail cannot wrap its nonempty payload.
theorem bytesTailValid_copyBounds {cd : ByteArray} {head : UInt256}
    (hsize : cd.size < 2 ^ 255) (hv : bytesTailValid cd head) :
    (head + (⟨32⟩ : UInt256)).toNat + (calldataWord cd head.toNat).toNat ≤ cd.size := by
  obtain ⟨hl, he⟩ := hv
  have hsz : cd.size < UInt256.size := by change _ < 2 ^ 256; omega
  rw [UInt256.toNat_ofNat_of_lt hsz] at he
  by_cases hh : cd.size ≤ head.toNat
  · rw [calldataWord_zero_of_ge cd head hh] at he ⊢
    simpa only [u256_add_zero, show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.add_zero] using he
  · have hhead : head.toNat + 32 < UInt256.size := by change _ < 2 ^ 256; omega
    have h32 : (head + (⟨32⟩ : UInt256)).toNat = head.toNat + 32 :=
      uadd_word_ofNat_toNat head 32 hhead
    have hend : (head + (⟨32⟩ : UInt256)).toNat +
        (calldataWord cd head.toNat).toNat < UInt256.size := by
      rw [h32]
      change _ ≤ 18446744073709551615 at hl
      change _ < 2 ^ 256
      omega
    rwa [uadd_toNat, Nat.mod_eq_of_lt hend] at he

-- LIBRARY CANDIDATE: signed comparison agrees with the unsigned bound below the sign bit.
theorem sgt_zero_of_nonnegative_le {a b : UInt256}
    (hb : b.toNat < 2 ^ 255) (hle : a.toNat ≤ b.toNat) : UInt256.sgt a b = ⟨0⟩ := by
  have ha : ¬ a.toNat ≥ 2 ^ 255 := by omega
  have hb' : ¬ b.toNat ≥ 2 ^ 255 := by omega
  have hn : ¬ a > b := by exact Nat.not_lt.mpr hle
  simp only [UInt256.sgt, UInt256.sgtBool, ha, hb', if_false, hn, decide_false]
  rfl

theorem bytesTailValid_signedGuard {cd : ByteArray} {head : UInt256}
    (hsize : cd.size < 2 ^ 255) (hv : bytesTailValid cd head) :
    UInt256.sgt (head + ⟨32⟩)
      (UInt256.ofNat cd.size - calldataWord cd head.toNat) = ⟨0⟩ := by
  have hbounds := bytesTailValid_copyBounds hsize hv
  have hsz : cd.size < UInt256.size := by change _ < 2 ^ 256; omega
  have hlen : (calldataWord cd head.toNat).toNat ≤ (UInt256.ofNat cd.size).toNat := by
    rw [UInt256.toNat_ofNat_of_lt hsz]
    omega
  have hsub : (UInt256.ofNat cd.size - calldataWord cd head.toNat).toNat =
      cd.size - (calldataWord cd head.toNat).toNat := by
    change (UInt256.sub (UInt256.ofNat cd.size) (calldataWord cd head.toNat)).toNat = _
    rw [usub_toNat hlen, UInt256.toNat_ofNat_of_lt hsz]
  exact sgt_zero_of_nonnegative_le (by rw [hsub]; omega) (by rw [hsub]; omega)

-- LIBRARY CANDIDATE: a padded read within the source is its ordinary slice.
theorem readBytes_eq_extract_of_bounds (cd : ByteArray) (start len : Nat)
    (h : start + len ≤ cd.size) : cd.readBytes start len = cd.extract start (start + len) := by
  apply byteArray_eq_of_toList_eq
  rw [readBytes_padded_toList]
  have hs : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  simp only [List.length_take, List.length_drop, hs,
    Nat.min_eq_left (show len ≤ cd.size - start by omega), Nat.sub_self,
    List.replicate_zero, List.append_nil]
  simp only [byteArray_toList_eq, ByteArray.data_extract, Array.toList_extract,
    List.extract_eq_take_drop, Nat.add_sub_cancel_left]

theorem bytesTailData_eq_extract {cd : ByteArray} {head : UInt256}
    (hsize : cd.size < 2 ^ 255) (hv : bytesTailValid cd head) :
    bytesTailData cd head = cd.extract (head + (⟨32⟩ : UInt256)).toNat
      ((head + (⟨32⟩ : UInt256)).toNat + (calldataWord cd head.toNat).toNat) := by
  by_cases hh : cd.size ≤ head.toNat
  · unfold bytesTailData
    rw [calldataWord_zero_of_ge cd head hh]
    apply byteArray_eq_of_toList_eq
    rw [readBytes_padded_toList, byteArray_extract_toList]
    simp only [show (⟨0⟩ : UInt256).toNat = 0 from rfl,
      List.take_zero, List.length_nil, Nat.sub_zero, List.replicate_zero, List.nil_append,
      Nat.add_zero, Nat.sub_self, List.take_zero]
  · have h32 : (head + (⟨32⟩ : UInt256)).toNat = head.toNat + 32 :=
      uadd_word_ofNat_toNat head 32 (by change _ < 2 ^ 256; omega)
    have hbounds := bytesTailValid_copyBounds hsize hv
    rw [h32] at hbounds ⊢
    exact readBytes_eq_extract_of_bounds cd _ _ hbounds

end Benchmarks.Morpho.MetaMorphoV1_1
