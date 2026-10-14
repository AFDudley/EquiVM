import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDecimalsSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStorageHeader
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_003
import Benchmarks.Morpho.MetaMorphoV1_1.CreationBlocks_009

/-! Choose the optional decimals result or 18, and initialize the ERC4626 immutables. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode
set_option autoImplicit false

def constructorUnderlyingDecimals (ok : Bool) (out : ByteArray) : UInt256 :=
  if constructorDecimalsValid ok out then calldataWord out 0 else ⟨18⟩

theorem constructorUnderlyingDecimals_bound (ok : Bool) (out : ByteArray) :
    (constructorUnderlyingDecimals ok out).toNat < 256 := by
  unfold constructorUnderlyingDecimals
  split
  · have := ‹constructorDecimalsValid ok out›.2.2
    omega
  · decide

def constructorUnderlyingExpr : Expr :=
  .ite (.tupleGet (.var "decimalResult") 0) (.tupleGet (.var "decimalResult") 1) (.intLit 18)

theorem constructorUnderlyingSource {frame : Frame} {evm : State} {ok : Bool} {out : ByteArray}
    (hget : frame.locals.get? "decimalResult" = some (constructorDecimalsValue ok out)) :
    evalExpr? config frame evm constructorUnderlyingExpr =
      .ok (uint256Value (constructorUnderlyingDecimals ok out)) := by
  by_cases hv : constructorDecimalsValid ok out
  · simp only [constructorUnderlyingExpr, constructorUnderlyingDecimals, constructorDecimalsValue,
      constructorDecimalsWord, hv, if_true, decide_true, evalExpr?, hget,
      EvalResult.ofOption, bind, EvalResult.bind, pure, tupleGetValue?]
    rfl
  · simp only [constructorUnderlyingExpr, constructorUnderlyingDecimals, constructorDecimalsValue,
      constructorDecimalsWord, hv, if_false, decide_false, evalExpr?, hget,
      EvalResult.ofOption, bind, EvalResult.bind, pure, tupleGetValue?]
    rfl

def constructorAssetFrame (frame : Frame) (asset : AccountAddress) (ok : Bool) (out : ByteArray) : Frame :=
  { frame with
    immutables :=
      (frame.immutables.insert "_underlyingDecimals" (uint256Value (constructorUnderlyingDecimals ok out))).insert
        "_asset" (.address asset) }

theorem constructorAssetSourcePrefix {frame : Frame} {evm : State} {asset : AccountAddress}
    {ok : Bool} {out : ByteArray} {rest : List Stmt} {result : ExecResult}
    (hcontract : frame.contract = contract)
    (hdecimal : frame.locals.get? "decimalResult" = some (constructorDecimalsValue ok out))
    (hasset : frame.locals.get? "assetAddress" = some (.address asset))
    (htail : ExecBlock config (constructorAssetFrame frame asset ok out) evm rest result) :
    ExecBlock config frame evm
      (.setImmutable "_underlyingDecimals" constructorUnderlyingExpr ::
        .setImmutable "_asset" (.var "assetAddress") :: rest) result := by
  apply ExecBlock.consNormal (ExecStmt.setImmutable
    (ty := .int (.uint ⟨8, by decide⟩)) (constructorUnderlyingSource hdecimal) ?_ ?_)
  · apply ExecBlock.consNormal (ExecStmt.setImmutable (value := .address asset) (ty := .address) ?_ ?_ rfl) htail
    · simp only [evalExpr?, hasset, EvalResult.ofOption]
    · change immutableType? frame.contract "_asset" = _
      rw [hcontract]
      rfl
  · rw [hcontract]
    rfl
  · have hb := constructorUnderlyingDecimals_bound ok out
    simp only [elemValueFits, decide_eq_true_eq]
    exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr hb⟩

theorem constructorUnderlyingRuntime {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (ok : Bool) (out : ByteArray) (hstack : R.length + 3 ≤ 1024)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨443⟩
      (constructorDecimalsWord ok out :: (if constructorDecimalsValid ok out then ⟨1⟩ else ⟨0⟩) :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨450⟩
      (constructorUnderlyingDecimals ok out :: R) mem aw' rdata σ k' C' := by
  by_cases hv : constructorDecimalsValid ok out
  · simp only [if_pos hv] at rd
    obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1Creation_block_443_fallthrough_packed hstack (by decide) rd
    refine ⟨aw1, k1, C1, ?_⟩
    simpa only [constructorUnderlyingDecimals, constructorDecimalsWord,
      if_pos hv, metaMorphoV1_1Creation_block_443_fallthrough_stack] using r1
  · simp only [if_neg hv] at rd
    have r1 := metaMorphoV1_1Creation_block_443_taken hstack (by decide) (by native_decide) rd
    obtain ⟨aw2, k2, C2, r2⟩ := metaMorphoV1_1Creation_block_2176_packed (by omega) (by native_decide) r1
    refine ⟨aw2, k2, C2, ?_⟩
    simpa only [constructorUnderlyingDecimals, if_neg hv,
      metaMorphoV1_1Creation_block_2176_stack] using r2

def constructorAssetMemory (mem : ByteArray) (asset : AccountAddress) (decimals : UInt256) : ByteArray :=
  writeWord (writeWord mem 160 decimals) 128 (UInt256.ofNat asset.val)

theorem constructorAssetRuntime {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨443⟩
      (constructorDecimalsWord ok out :: (if constructorDecimalsValid ok out then ⟨1⟩ else ⟨0⟩) ::
        constructorMetadataTail a a.stringsEnd true) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨2802⟩
      (UInt256.ofNat a.stringsEnd :: ⟨466⟩ :: constructorMetadataTail a a.stringsEnd true)
      (constructorAssetMemory mem a.asset (constructorUnderlyingDecimals ok out)) aw' rdata σ k' C' := by
  obtain ⟨_, _, _, r1⟩ := constructorUnderlyingRuntime ok out (by simp [constructorMetadataTail]) rd
  exact metaMorphoV1_1Creation_block_450_packed (by simp) (by native_decide) r1

end Benchmarks.Morpho.MetaMorphoV1_1
