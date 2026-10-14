import Benchmarks.Morpho.MetaMorphoV1_1.OptionalReturnSource
import Reasoning.ExternalCall

/-! SafeERC20's probing call short-circuits failed calls and validates nonempty ABI Booleans. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def optionalBoolDecodable (ok : Bool) (out : ByteArray) : Prop :=
  ok = false ∨ out.size = 0 ∨ BoolReturnValid out

instance (ok : Bool) (out : ByteArray) : Decidable (optionalBoolDecodable ok out) := by
  unfold optionalBoolDecodable BoolReturnValid
  infer_instance

def optionalBoolValue (σ : AccountMap) (token : UInt256) (ok : Bool) (out : ByteArray) : Bool :=
  decide (ok = true ∧ optionalReturnValid out ∧ extCodeSizeWord σ token ≠ ⟨0⟩)

def optionalBoolExpr : Expr :=
  .binary .and
    (.binary .and (.var "success")
      (.binary .or (.binary .eq returnBytesLength (.intLit 0))
        (.abiDecode abiBool (.var "returndata"))))
    (.binary .gt (.extCodeSize (.var "token")) (.intLit 0))

theorem optionalBoolSource {frame : Frame} {evm : State} {token : AccountAddress}
    {ok : Bool} {out : ByteArray}
    (htoken : frame.locals.get? "token" = some (.address token))
    (hok : frame.locals.get? "success" = some (.bool ok))
    (hout : frame.locals.get? "returndata" = some (.bytes out))
    (hsize : out.size < 2 ^ 255) (hvalid : optionalBoolDecodable ok out) :
    evalExpr? config frame evm optionalBoolExpr =
      .ok (.bool (optionalBoolValue evm.accountMap (UInt256.ofNat token.toNat) ok out)) := by
  have hs : evalExpr? config frame evm (.var "success") = .ok (.bool ok) := by
    simp only [evalExpr?, hok, EvalResult.ofOption]
  have hl : evalExpr? config frame evm (.binary .eq returnBytesLength (.intLit 0)) =
      .ok (.bool (decide (out.size = 0))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide)]
    simp only [returnBytesLengthSource hout, evalExpr?, bind, EvalResult.bind, pure]
    simp [evalBinaryOp?, BEq.beq]
  have hc := evalExpr_codeGuard_of_accounts_eq (cfg := config) (frame := frame)
    (target := UInt256.ofNat token.toNat) rfl
    (by rw [accountAddress_ofUInt256_eq_ofNat_toNat]; exact (accountAddress_of_word_val token).symm)
    (show evalExpr? config frame evm (.var "token") = .ok (.address token) by
      simp only [evalExpr?, htoken, EvalResult.ofOption])
  have hziff : 0 < (extCodeSizeWord evm.accountMap (UInt256.ofNat token.toNat)).toNat ↔
      extCodeSizeWord evm.accountMap (UInt256.ofNat token.toNat) ≠ ⟨0⟩ := by
    constructor
    · intro h he; rw [he] at h; exact Nat.not_lt_zero _ h
    · intro h; by_contra hn; exact h (uint256_toNat_eq_zero (by omega))
  simp only [hziff] at hc
  cases ok with
  | false =>
      simp only [optionalBoolExpr, optionalBoolValue, evalExpr?, hs, bind, EvalResult.bind]
      simp [pure]
  | true =>
      by_cases hz : out.size = 0
      · simp only [hz, decide_true] at hl
        simpa only [optionalBoolExpr, optionalBoolValue, optionalReturnValid, hz,
          true_or, true_and, and_self, evalExpr?, hs, hl, hc, bind, EvalResult.bind, pure]
      · have hb : BoolReturnValid out := (hvalid.resolve_left (by decide)).resolve_left hz
        have hd := returnBoolSource (evm := evm) hout (decodeReturnBool_valid hb hsize)
        simp only [hz, decide_false] at hl
        rcases hb.2 with hw | hw
        · simp only [hw, ne_eq, not_true_eq_false, decide_false] at hd
          simp only [optionalBoolExpr, evalExpr?, hs, hl, hd, bind, EvalResult.bind]
          simp only [optionalBoolValue, optionalReturnValid, hz, hw,
            show (⟨0⟩ : UInt256) ≠ ⟨1⟩ by decide, false_or, and_false, false_and,
            decide_false, pure]
        · simp only [hw, ne_eq, show (⟨1⟩ : UInt256) ≠ ⟨0⟩ by decide,
            not_false_eq_true, decide_true] at hd
          simpa only [optionalBoolExpr, optionalBoolValue, optionalReturnValid, hz, hw, hb.1,
            false_or, and_self, true_and, evalExpr?, hs, hl, hd, hc, bind, EvalResult.bind, pure]

theorem optionalBoolSourceReverts {frame : Frame} {evm : State} {out : ByteArray}
    (hok : frame.locals.get? "success" = some (.bool true))
    (hout : frame.locals.get? "returndata" = some (.bytes out))
    (hsize : out.size < 2 ^ 255) (hbad : ¬ optionalBoolDecodable true out) :
    evalExpr? config frame evm optionalBoolExpr = .revert := by
  have hz : out.size ≠ 0 := fun h => hbad (.inr (.inl h))
  have hd := returnBoolSourceRevert (evm := evm) hout
    (decodeReturnBool_invalid (fun h => hbad (.inr (.inr h))) hsize)
  have hs : evalExpr? config frame evm (.var "success") = .ok (.bool true) := by
    simp only [evalExpr?, hok, EvalResult.ofOption]
  have hl : evalExpr? config frame evm (.binary .eq returnBytesLength (.intLit 0)) =
      .ok (.bool false) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide)]
    simp only [returnBytesLengthSource hout, evalExpr?, bind, EvalResult.bind, pure]
    simp [evalBinaryOp?, BEq.beq, hz]
  simp only [optionalBoolExpr, evalExpr?, hs, hl, hd, bind, EvalResult.bind]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
