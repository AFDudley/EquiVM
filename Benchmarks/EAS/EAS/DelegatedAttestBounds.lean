import Benchmarks.EAS.EAS.DelegatedAttestDecode
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: a successful signed decoder guard bounds a nonnegative input pointer.
theorem calldataHead192_bound {cd : ByteArray} {head : UInt256}
    (hs : cd.size < UInt256.size) (hh : head.toNat < 2^255)
    (hc : UInt256.slt (UInt256.sub (UInt256.ofNat cd.size) head) ⟨192⟩ = ⟨0⟩) :
    head.toNat+192 ≤ cd.size := by
  by_cases he : head.toNat ≤ cd.size
  · by_contra hn
    have hbad := solcDecodeLenCheckShort (head := head) (need := (⟨192⟩ : UInt256)) he (by change cd.size < head.toNat+192; omega) hs (by decide)
    have hzeroOne : (⟨0⟩ : UInt256) = ⟨1⟩ := hc.symm.trans hbad
    exact (by decide : (⟨0⟩ : UInt256) ≠ ⟨1⟩) hzeroOne
  · exfalso
    have hu : (UInt256.sub (UInt256.ofNat cd.size) head).toNat = UInt256.size+cd.size-head.toNat := by
      rw [usub_toNat_underflow (by rw [ulit_toNat' _ hs]; omega),ulit_toNat' _ hs]
    have hbad := slt_lit_one_high (a := UInt256.sub (UInt256.ofNat cd.size) head) (m := 192)
      (by decide) (by rw [hu]; change 2^255 ≤ 2^256+cd.size-head.toNat; omega)
    have hzeroOne : (⟨0⟩ : UInt256) = ⟨1⟩ := hc.symm.trans hbad
    exact (by decide : (⟨0⟩ : UInt256) ≠ ⟨1⟩) hzeroOne

-- A copied request that passed its eager decoder also passes the later calldata reference check.
theorem requestReference_of_eager {cd : ByteArray} {root : UInt256}
    (hs : cd.size < 2^255+4) (hlo : 4 ≤ root.toNat) (hh : root.toNat < 2^254)
    (ho : (calldataWord cd (root+UInt256.ofNat 32).toNat).toNat ≤ 2^64-1)
    (hd : requestDataValid cd (delegatedAttestData cd root)) :
    requestReferenceValid cd root (root+UInt256.ofNat 32) := by
  let off := calldataWord cd (root+UInt256.ofNat 32).toNat
  have hsize : cd.size < UInt256.size := by change cd.size < 2^256; omega
  have hp : (delegatedAttestData cd root).toNat = root.toNat+off.toNat := by
    change (root+off).toNat = _
    rw [uadd_toNat,Nat.mod_eq_of_lt (by change root.toNat+off.toNat < 2^256; change off.toNat ≤ 2^64-1 at ho; omega)]
  have hb := calldataHead192_bound hsize (by rw [hp]; change off.toNat ≤ 2^64-1 at ho; omega) hd.1
  rw [hp] at hb
  have hn : ((UInt256.ofNat cd.size-root)-⟨191⟩).toNat = cd.size-root.toNat-191 := by
    have hn0 : (UInt256.sub (UInt256.ofNat cd.size) root).toNat = cd.size-root.toNat := usub_ofNat_word_toNat (by omega) hsize
    change (UInt256.sub (UInt256.sub (UInt256.ofNat cd.size) root) ⟨191⟩).toNat = _
    rw [usub_toNat (by rw [hn0]; change 191 ≤ cd.size-root.toNat; omega),hn0]
    rfl
  have he : UInt256.slt off ((UInt256.ofNat cd.size-root)-⟨191⟩) = ⟨1⟩ := by
    have he : UInt256.sltBool off ((UInt256.ofNat cd.size-root)-⟨191⟩) = true := by
      unfold UInt256.sltBool
      rw [if_neg (show ¬ off.toNat ≥ 2^255 by change off.toNat ≤ 2^64-1 at ho; omega),
        if_neg (show ¬ ((UInt256.ofNat cd.size-root)-⟨191⟩).toNat ≥ 2^255 by rw [hn]; omega)]
      apply decide_eq_true
      change off.toNat < ((UInt256.ofNat cd.size-root)-⟨191⟩).toNat
      rw [hn]; omega
    change UInt256.fromBool (UInt256.sltBool off ((UInt256.ofNat cd.size-root)-⟨191⟩)) = ⟨1⟩
    rw [he]
    rfl
  change UInt256.isZero (UInt256.slt off ((UInt256.ofNat cd.size-root)-⟨191⟩)) = ⟨0⟩
  rw [he]
  rfl

theorem delegatedAttestRoot_bounds {cd : ByteArray} (ho : (calldataWord cd 4).toNat ≤ 2^64-1) :
    4 ≤ (attestRoot cd).toNat ∧ (attestRoot cd).toNat ≤ 2^64+3 := by
  have hn : (attestRoot cd).toNat = 4+(calldataWord cd 4).toNat := by
    rw [attestRoot,uadd_toNat,Nat.mod_eq_of_lt (by change 4+(calldataWord cd 4).toNat < 2^256; omega)]
    rfl
  rw [hn]
  omega

-- LIBRARY CANDIDATE: reassociate two modular word subtractions.
theorem word_sub_sub_comm (a b c : UInt256) : UInt256.sub (UInt256.sub a b) c = UInt256.sub a (c+b) := by
  apply u256_inj
  change ((a.val-b.val)-c.val).val = (a.val-(c.val+b.val)).val
  apply congrArg Fin.val
  abel

-- Normalize the compiler's reassociated tuple-head subtraction.
theorem delegatedAttestHead_sub (size off : UInt256) :
    UInt256.sub size off+UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932 =
      UInt256.sub size (UInt256.ofNat 4+off) := by
  have hn : UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639932 =
      ⟨-(UInt256.ofNat 4).val⟩ := by native_decide
  rw [hn,← word_sub_eq_add_neg]
  exact word_sub_sub_comm size off (UInt256.ofNat 4)

end Benchmarks.EAS.EAS
