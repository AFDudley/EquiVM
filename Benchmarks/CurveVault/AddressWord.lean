import Benchmarks.CurveVault.Common

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATES: canonical word representation and round trip for any address.
theorem addressWord_toNat (a : AccountAddress) : (UInt256.ofNat a.val).toNat = a.val :=
  ulit_toNat' _ (lt_trans a.isLt (by decide +kernel : AccountAddress.size < UInt256.size))

theorem addressWord_canonical (a : AccountAddress) : (UInt256.ofNat a.val).toNat < EVM.addressModulus := by
  rw [addressWord_toNat]
  exact a.isLt

theorem addressWord_roundtrip (a : AccountAddress) : AccountAddress.ofNat (UInt256.ofNat a.val).toNat = a := by
  apply Fin.ext
  change (UInt256.ofNat a.val).toNat % AccountAddress.size = a.val
  rw [addressWord_toNat, Nat.mod_eq_of_lt a.isLt]

theorem addressOfWord_eq_iff {w : UInt256} (hcanon : w.toNat < EVM.addressModulus) (a : AccountAddress) :
    AccountAddress.ofNat w.toNat = a ↔ w = UInt256.ofNat a.val := by
  constructor
  · intro h
    have hk := keyValueToWord_address_of_canonical w hcanon
    rw [h, keyValueToWord_address] at hk
    exact hk.symm
  · intro h
    rw [h, addressWord_roundtrip]

-- LIBRARY CANDIDATE: address inequality evaluated against a canonical EVM word.
theorem evalExpr_ne_address_word {cfg : Config} {stele : Frame} {evm : State}
    {lhs rhs : Expr} {word : UInt256} {addr : AccountAddress}
    (hcanon : word.toNat < EVM.addressModulus)
    (hl : evalExpr? cfg stele evm lhs = .ok (.address (AccountAddress.ofNat word.toNat)))
    (hr : evalExpr? cfg stele evm rhs = .ok (.address addr)) :
    evalExpr? cfg stele evm (.binary .ne lhs rhs) =
      .ok (.bool (decide (word ≠ UInt256.ofNat addr.val))) := by
  rw [evalExpr_binary_nonshort (by decide +kernel) (by decide +kernel), hl, hr]
  simp only [EvalResult.bind, bind, evalBinaryOp?, value_address_beq]
  simp [addressOfWord_eq_iff hcanon addr]

end Benchmarks.CurveVault
