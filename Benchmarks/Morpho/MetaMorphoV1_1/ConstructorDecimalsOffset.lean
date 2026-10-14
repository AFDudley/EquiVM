import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStrictDecimalsInit

/-! The final decimal offset is the natural-number difference `18 - assetDecimals`. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def constructorDecimalsOffset (decimals : UInt256) : UInt256 := UInt256.ofNat (18 - decimals.toNat)

theorem constructorDecimalsOffset_nat (decimals : UInt256) :
    (constructorDecimalsOffset decimals).toNat = 18 - decimals.toNat :=
  UInt256.toNat_ofNat_of_lt (by change 18 - decimals.toNat < 2 ^ 256; omega)

theorem constructorDecimalsOffset_bound (decimals : UInt256) :
    (constructorDecimalsOffset decimals).toNat < 256 := by
  rw [constructorDecimalsOffset_nat]; omega

theorem constructorDecimalsOffset_word (decimals : UInt256) (hv : decimals.toNat < 256) :
    UInt256.land (UInt256.mul (UInt256.gt (UInt256.ofNat 18)
      (UInt256.land decimals (UInt256.ofNat 255)))
      (UInt256.sub (UInt256.ofNat 18) (UInt256.land decimals (UInt256.ofNat 255))))
      (UInt256.ofNat 255) = constructorDecimalsOffset decimals := by
  have hm : decimals.land (UInt256.ofNat 255) = decimals := lowByteClean hv
  rw [hm]
  by_cases hl : decimals.toNat < 18
  · rw [ugt_one hl]
    have he : UInt256.mul ⟨1⟩ (UInt256.sub (UInt256.ofNat 18) decimals) =
        constructorDecimalsOffset decimals := by
      apply u256_inj
      have hs : (UInt256.sub (UInt256.ofNat 18) decimals).toNat = 18 - decimals.toNat :=
        usub_toNat (by change decimals.toNat ≤ 18; omega)
      rw [u256_mul_toNat, hs, constructorDecimalsOffset_nat]
      change (1 * (18 - decimals.toNat)) % UInt256.size = _
      rw [one_mul, Nat.mod_eq_of_lt (by change 18 - decimals.toNat < 2 ^ 256; omega)]
    rw [he]
    exact lowByteClean (constructorDecimalsOffset_bound decimals)
  · rw [ugt_zero (by change 18 ≤ decimals.toNat; omega), u256_mul_zero_left]
    rw [constructorDecimalsOffset, Nat.sub_eq_zero_of_le (by omega)]
    rfl

def constructorDecimalsOffsetExpr : Expr :=
  .cast (.ite (.binary .gt (.intLit 18) (.var "assetDecimals"))
    (.binary .sub (.intLit 18) (.var "assetDecimals")) (.intLit 0))
    (.elem (.int (.uint ⟨8, by decide⟩)))

def constructorOffsetFrame (frame : Frame) (decimals : UInt256) : Frame :=
  { frame with
    immutables := frame.immutables.insert "DECIMALS_OFFSET"
      (uint256Value (constructorDecimalsOffset decimals)) }

theorem constructorDecimalsOffset_eval {frame : Frame} {evm : State} {decimals : UInt256}
    (hget : frame.locals.get? "assetDecimals" = some (uint256Value decimals)) :
    evalExpr? config frame evm constructorDecimalsOffsetExpr =
      .ok (uint256Value (constructorDecimalsOffset decimals)) := by
  have hn := constructorDecimalsOffset_nat decimals
  have hi : evalExpr? config frame evm
      (.ite (.binary .gt (.intLit 18) (.var "assetDecimals"))
        (.binary .sub (.intLit 18) (.var "assetDecimals")) (.intLit 0)) =
      .ok (uint256Value (constructorDecimalsOffset decimals)) := by
    by_cases hl : decimals.toNat < 18
    · have hc : (18 : Int) > Int.ofNat decimals.toNat := by
        simp only [Int.ofNat_eq_natCast]; omega
      have hd : (18 : Int) - Int.ofNat decimals.toNat = Int.ofNat (18 - decimals.toNat) := by
        simp only [Int.ofNat_eq_natCast]; omega
      simp only [evalExpr?, hget, EvalResult.ofOption, uint256Value, hn, evalBinaryOp?,
        bind, EvalResult.bind, pure, hc, decide_true, hd]
    · have hc : ¬ (18 : Int) > Int.ofNat decimals.toNat := by
        simp only [Int.ofNat_eq_natCast]; omega
      have hz : 18 - decimals.toNat = 0 := by omega
      simp only [evalExpr?, hget, EvalResult.ofOption, uint256Value, hn, evalBinaryOp?,
        bind, EvalResult.bind, pure, hc, decide_false, hz]
      rfl
  simp only [constructorDecimalsOffsetExpr, evalExpr?, hi, bind, EvalResult.bind,
    uint256Value, castValue_int, EvalResult.ofOption]
  congr 2
  change (Int.ofNat (constructorDecimalsOffset decimals).toNat) % 256 = _
  exact Int.emod_eq_of_lt (Int.natCast_nonneg _)
    (Int.ofNat_lt.mpr (constructorDecimalsOffset_bound decimals))

theorem constructorDecimalsOffsetPrefix {frame : Frame} {evm : State} {decimals : UInt256}
    {result : ExecResult} (hc : frame.contract = contract)
    (hget : frame.locals.get? "assetDecimals" = some (uint256Value decimals))
    (hrest : ExecBlock config (constructorOffsetFrame frame decimals) evm
      (contract.ctor.body.drop 37) result) :
    ExecBlock config frame evm (contract.ctor.body.drop 36) result := by
  change ExecBlock config frame evm
    (.setImmutable "DECIMALS_OFFSET" constructorDecimalsOffsetExpr :: contract.ctor.body.drop 37) result
  apply ExecBlock.consNormal (ExecStmt.setImmutable
    (ty := .int (.uint ⟨8, by decide⟩)) (constructorDecimalsOffset_eval hget)
    (by rw [hc]; rfl) ?_) hrest
  simp only [elemValueFits, decide_eq_true_eq]
  exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr (constructorDecimalsOffset_bound decimals)⟩

end Benchmarks.Morpho.MetaMorphoV1_1
