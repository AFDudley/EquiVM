import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDomainReserveSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorAssetInit
import Benchmarks.Morpho.MetaMorphoV1_1.AccessControl

/-! Source domain-cache writes and the initial-owner guard. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def constructorOwnerGuardExpr : Expr :=
  .binary .ne (.var "owner") (.cast (.intLit 0) (.elem .address))

theorem constructorOwnerGuardSource {frame : Frame} {evm : State} {owner : AccountAddress}
    (hget : frame.locals.get? "owner" = some (.address owner)) :
    evalExpr? config frame evm constructorOwnerGuardExpr =
      .ok (.bool (decide (owner ≠ ⟨0, by decide⟩))) := by
  apply evalExpr_addressNe
  · simp only [evalExpr?, hget, EvalResult.ofOption]
  · simp only [evalExpr?, pure, bind, EvalResult.bind, castValue?]
    rfl

theorem constructorInputFrame_owner (a : ConstructorArgs) (cursors : List UInt256) :
    (constructorInputFrame a cursors).locals.get? "owner" = some (.address a.owner) := by
  induction cursors with
  | nil =>
    apply Std.HashMap.getElem?_ofList_of_mem (k := "owner") (by decide)
    · simp
    · simp
  | cons _ _ ih =>
    rw [constructorInputFrame, store_get_ne _ _ (by decide : (cursorName == "owner") = false)]
    exact ih

theorem constructorAssetReadyFrame_owner (a : ConstructorArgs) (ok : Bool) (out : ByteArray) :
    (constructorAssetReadyFrame a ok out).locals.get? "owner" = some (.address a.owner) := by
  have ho := cursorResultFrame_preserves (constructorReadyFrame a) "decimalResult" "owner"
    (constructorDecimalsValue ok out) (constructorDecimalsCursor a out)
    (by decide) (by decide) (by decide)
  exact ho.trans (constructorInputFrame_owner a _)

theorem constructorDomainCacheBodySplit : contract.ctor.body.drop 21 =
    constructorDomainCacheBody ++ .require constructorOwnerGuardExpr :: contract.ctor.body.drop 25 := rfl

theorem constructorDomainCachedFrame_owner {frame : Frame} {owner : AccountAddress}
    (I : ExecutionEnv) (hget : frame.locals.get? "owner" = some (.address owner)) :
    (constructorDomainCachedFrame frame I).locals.get? "owner" = some (.address owner) := by
  rw [constructorDomainCachedFrame, store_get_ne _ _ (by decide)]
  exact hget

theorem constructorDomainOwnerReverts {frame : Frame} {evm : State} {owner : AccountAddress}
    (hcontract : frame.contract = contract)
    (hname : frame.immutables.get? "_hashedName" = some (uint256Value constructorNameHash))
    (hversion : frame.immutables.get? "_hashedVersion" = some (uint256Value constructorVersionHash))
    (howner : frame.locals.get? "owner" = some (.address owner))
    (hzero : owner = ⟨0, by decide⟩) (rest : List Stmt) :
    ExecBlock config frame evm
      (constructorDomainCacheBody ++ .require constructorOwnerGuardExpr :: rest) .reverted := by
  apply execBlock_append (constructorDomainCacheSource evm hcontract hname hversion)
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [hzero, ne_eq, not_true_eq_false, decide_false] using
    constructorOwnerGuardSource (evm := evm) (constructorDomainCachedFrame_owner evm.executionEnv howner)

theorem constructorDomainOwnerPrefix {frame : Frame} {evm : State} {owner : AccountAddress}
    {rest : List Stmt} {result : ExecResult}
    (hcontract : frame.contract = contract)
    (hname : frame.immutables.get? "_hashedName" = some (uint256Value constructorNameHash))
    (hversion : frame.immutables.get? "_hashedVersion" = some (uint256Value constructorVersionHash))
    (howner : frame.locals.get? "owner" = some (.address owner))
    (hnonzero : owner ≠ ⟨0, by decide⟩)
    (htail : ExecBlock config (constructorDomainCachedFrame frame evm.executionEnv) evm rest result) :
    ExecBlock config frame evm
      (constructorDomainCacheBody ++ .require constructorOwnerGuardExpr :: rest) result := by
  apply execBlock_append (constructorDomainCacheSource evm hcontract hname hversion)
  apply ExecBlock.consNormal (ExecStmt.requireTrue ?_) htail
  simpa only [ne_eq, hnonzero, not_false_eq_true, decide_true] using
    constructorOwnerGuardSource (evm := evm) (constructorDomainCachedFrame_owner evm.executionEnv howner)

end Benchmarks.Morpho.MetaMorphoV1_1
