import Benchmarks.CurveVault.SymbolReturnMemory

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.CurveVault

theorem symbolOffset_noOverflow (offset : UInt256)
    (h : UInt256.lt (UInt256.ofNat 288 + offset) (UInt256.ofNat 288) = ⟨0⟩) :
    288 + offset.toNat < UInt256.size := by
  by_contra hn
  have hover := u256_add_overflow_lt (UInt256.ofNat 288) offset
    (show UInt256.size ≤ (UInt256.ofNat 288).toNat + offset.toNat by change UInt256.size ≤ 288 + offset.toNat; omega)
  rw [hover] at h
  exact (by decide +kernel : (⟨1⟩ : UInt256) ≠ ⟨0⟩) h

theorem symbolChecks_bounds (offset size : UInt256) (len : Nat) (hlen : len ≤ 96)
    (h425 : UInt256.lt (UInt256.ofNat 288 + offset) (UInt256.ofNat 288) = ⟨0⟩)
    (hsmall : (UInt256.ofNat 288 + offset).toNat < 2 ^ 160)
    (h441 : UInt256.gt ((UInt256.ofNat 288 + offset) + (UInt256.ofNat 32 + size))
      (UInt256.ofNat 288 + UInt256.ofNat len) = ⟨0⟩)
    (h468 : UInt256.gt size (UInt256.ofNat 32) = ⟨0⟩) :
    size.toNat ≤ 32 ∧ offset.toNat + 32 + size.toNat ≤ len := by
  have hn : size.toNat ≤ 32 := ugt_eq_zero_to_le h468
  have hoff := symbolOffset_noOverflow offset h425
  have hp : (UInt256.ofNat 288 + offset).toNat = 288 + offset.toNat :=
    addWord_toNat _ _ hoff
  have hsz : (UInt256.ofNat 32 + size).toNat = 32 + size.toNat :=
    addWord_toNat _ _ (by change 32 + size.toNat < 2 ^ 256; omega)
  have he := ugt_eq_zero_to_le h441
  have hsum : ((UInt256.ofNat 288 + offset) + (UInt256.ofNat 32 + size)).toNat =
      288 + offset.toNat + (32 + size.toNat) := by
    rw [uadd_toNat, hp, hsz, Nat.mod_eq_of_lt (by change _ < 2 ^ 256; rw [hp] at hsmall; omega)]
  have hend : (UInt256.ofNat 288 + UInt256.ofNat len).toNat = 288 + len :=
    uadd_ofNat_toNat (by decide +kernel) (by change len < 2 ^ 256; omega)
      (by change 288 + len < 2 ^ 256; omega)
  rw [hsum, hend] at he
  exact ⟨hn, by omega⟩

theorem symbolChecks_of_bounds (offset size : UInt256) (len : Nat) (hlen : len ≤ 96)
    (hn : size.toNat ≤ 32) (he : offset.toNat + 32 + size.toNat ≤ len) :
    UInt256.lt (UInt256.ofNat 288 + offset) (UInt256.ofNat 288) = ⟨0⟩ ∧
    UInt256.gt ((UInt256.ofNat 288 + offset) + (UInt256.ofNat 32 + size))
      (UInt256.ofNat 288 + UInt256.ofNat len) = ⟨0⟩ ∧
    UInt256.gt size (UInt256.ofNat 32) = ⟨0⟩ := by
  have hp : (UInt256.ofNat 288 + offset).toNat = 288 + offset.toNat :=
    addWord_toNat _ _ (by change 288 + offset.toNat < 2 ^ 256; omega)
  have hsz : (UInt256.ofNat 32 + size).toNat = 32 + size.toNat :=
    addWord_toNat _ _ (by change 32 + size.toNat < 2 ^ 256; omega)
  have hsum : ((UInt256.ofNat 288 + offset) + (UInt256.ofNat 32 + size)).toNat =
      288 + offset.toNat + (32 + size.toNat) := by
    rw [uadd_toNat, hp, hsz, Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)]
  have hend : (UInt256.ofNat 288 + UInt256.ofNat len).toNat = 288 + len :=
    uadd_ofNat_toNat (by decide +kernel) (by change len < 2 ^ 256; omega)
      (by change 288 + len < 2 ^ 256; omega)
  refine ⟨ult_zero ?_, ugt_zero ?_, ugt_zero hn⟩
  · rw [hp]
    change 288 ≤ 288 + offset.toNat
    omega
  · rw [hsum, hend]
    omega

theorem vaultSymbolValidChecks (mem out : ByteArray) (hmem : mem.size = 320)
    (h32 : 32 ≤ out.size) (hvalid : decodeTokenSymbol out ≠ none) :
    let m := vaultSymbolCallMemory mem out
    let offset := memLoad (UInt256.ofNat 288) m
    let ptr := UInt256.ofNat 288 + offset
    let size := memLoad ptr m
    UInt256.lt ptr (UInt256.ofNat 288) = ⟨0⟩ ∧
    UInt256.gt (ptr + (UInt256.ofNat 32 + size))
      (UInt256.ofNat 288 + UInt256.ofNat (min out.size 96)) = ⟨0⟩ ∧
    UInt256.gt size (UInt256.ofNat 32) = ⟨0⟩ := by
  obtain ⟨hfull, hn, he⟩ := decodeTokenSymbol_bounds out h32 hvalid
  let offset := memLoad (UInt256.ofNat 0) (out.extract 0 96)
  have hc : (out.extract 0 96).size = min out.size 96 := by rw [ByteArray.size_extract]; omega
  rw [hc] at hfull he
  have hoff : 288 + offset.toNat < UInt256.size := by change 288 + offset.toNat < 2 ^ 256; dsimp only [offset]; omega
  have hp : UInt256.ofNat 288 + offset = UInt256.ofNat (288 + offset.toNat) := by
    apply u256_inj
    rw [uadd_toNat, show (UInt256.ofNat 288).toNat = 288 from rfl,
      Nat.mod_eq_of_lt hoff, ulit_toNat' _ hoff]
  have hhead := vaultSymbolCallMemory_load mem out 0 hmem h32 (by decide +kernel)
  change memLoad (UInt256.ofNat 288) (vaultSymbolCallMemory mem out) = offset at hhead
  have hsize : memLoad (UInt256.ofNat 288 + offset) (vaultSymbolCallMemory mem out) =
      memLoad (UInt256.ofNat offset.toNat) (out.extract 0 96) := by
    rw [hp]
    exact vaultSymbolCallMemory_load mem out offset.toNat hmem h32 hoff
  dsimp only
  rw [hhead, hsize]
  exact symbolChecks_of_bounds offset _ _ (by omega) hn he

end Benchmarks.CurveVault
