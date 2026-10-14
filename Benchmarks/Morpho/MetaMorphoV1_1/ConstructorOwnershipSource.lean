import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorOwnerSource
import Benchmarks.Morpho.MetaMorphoV1_1.Ownership

/-! Apply the shared ownership function and continue past the constructor's Morpho guard. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def constructorOwnershipFrame (frame : Frame) : Frame :=
  { frame with locals := frame.locals.insert "initOwner" .unit }

theorem constructorOwnershipSource {frame : Frame} {evm : State} (owner : AccountAddress)
    (hcontract : frame.contract = contract)
    (howner : frame.locals.get? "owner" = some (.address owner)) :
    ExecStmt config frame evm (.internalCall "_transferOwnership" [.var "owner"] "initOwner")
      (.ok (constructorOwnershipFrame frame) (ownershipState evm (UInt256.ofNat owner.val))) := by
  rcases frame with ⟨decl, locals, imms⟩
  change decl = contract at hcontract
  subst decl
  have hr : AccountAddress.ofNat (UInt256.ofNat owner.val).toNat = owner :=
    accountAddress_of_word_val owner
  exact ownershipCall evm locals imms (UInt256.ofNat owner.val) "initOwner" (.var "owner")
    (addressWord_val_canonical owner)
    (by rw [hr]; simp only [evalExpr?, howner, EvalResult.ofOption])

theorem SourceState.constructorOwnership {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (owner : AccountAddress) :
    SourceState s0 I (ownershipAccounts I σ (UInt256.ofNat owner.val))
      (ownershipState evm (UInt256.ofNat owner.val)) := by
  have h1 := hs.readModifyWrite ⟨9⟩ (fun old ↦ setAddressOffset0Word old ⟨0⟩)
  have h2 := h1.readModifyWrite ⟨8⟩ (fun old ↦ setAddressOffset0Word old (UInt256.ofNat owner.val))
  exact h2

def constructorMorphoGuardExpr : Expr :=
  .binary .ne (.var "morpho") (.cast (.intLit 0) (.elem .address))

theorem constructorMorphoGuardSource {frame : Frame} {evm : State} {morpho : AccountAddress}
    (hget : frame.locals.get? "morpho" = some (.address morpho)) :
    evalExpr? config frame evm constructorMorphoGuardExpr =
      .ok (.bool (decide (morpho ≠ ⟨0, by decide⟩))) := by
  apply evalExpr_addressNe
  · simp only [evalExpr?, hget, EvalResult.ofOption]
  · simp only [evalExpr?, pure, bind, EvalResult.bind, castValue?]
    rfl

theorem constructorOwnershipBodySplit : contract.ctor.body.drop 25 =
    .internalCall "_transferOwnership" [.var "owner"] "initOwner" ::
      .require constructorMorphoGuardExpr :: contract.ctor.body.drop 27 := rfl

theorem constructorOwnershipFrame_morpho {frame : Frame} {morpho : AccountAddress}
    (hget : frame.locals.get? "morpho" = some (.address morpho)) :
    (constructorOwnershipFrame frame).locals.get? "morpho" = some (.address morpho) := by
  rw [constructorOwnershipFrame, store_get_ne _ _ (by decide)]
  exact hget

theorem constructorOwnershipReverts {frame : Frame} {evm : State} {owner morpho : AccountAddress}
    (hcontract : frame.contract = contract)
    (howner : frame.locals.get? "owner" = some (.address owner))
    (hmorpho : frame.locals.get? "morpho" = some (.address morpho))
    (hzero : morpho = ⟨0, by decide⟩) :
    ExecBlock config frame evm (contract.ctor.body.drop 25) .reverted := by
  rw [constructorOwnershipBodySplit]
  apply ExecBlock.consNormal (constructorOwnershipSource owner hcontract howner)
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [hzero, ne_eq, not_true_eq_false, decide_false] using
    constructorMorphoGuardSource (evm := ownershipState evm (UInt256.ofNat owner.val))
      (constructorOwnershipFrame_morpho hmorpho)

theorem constructorOwnershipPrefix {frame : Frame} {evm : State} {owner morpho : AccountAddress}
    {result : ExecResult} (hcontract : frame.contract = contract)
    (howner : frame.locals.get? "owner" = some (.address owner))
    (hmorpho : frame.locals.get? "morpho" = some (.address morpho))
    (hnonzero : morpho ≠ ⟨0, by decide⟩)
    (htail : ExecBlock config (constructorOwnershipFrame frame)
      (ownershipState evm (UInt256.ofNat owner.val)) (contract.ctor.body.drop 27) result) :
    ExecBlock config frame evm (contract.ctor.body.drop 25) result := by
  rw [constructorOwnershipBodySplit]
  apply ExecBlock.consNormal (constructorOwnershipSource owner hcontract howner)
  apply ExecBlock.consNormal (ExecStmt.requireTrue ?_) htail
  simpa only [ne_eq, hnonzero, not_false_eq_true, decide_true] using
    constructorMorphoGuardSource (evm := ownershipState evm (UInt256.ofNat owner.val))
      (constructorOwnershipFrame_morpho hmorpho)

end Benchmarks.Morpho.MetaMorphoV1_1
