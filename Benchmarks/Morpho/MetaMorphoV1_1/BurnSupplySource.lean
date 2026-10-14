import Benchmarks.Morpho.MetaMorphoV1_1.BalanceUpdateSource

/-! The burning branch of the ERC20 update helper. Supply is read after debiting the
balance, preserving the compiler's storage order without a noncollision assumption. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def burnSupplyState (evm : State) (value : UInt256) : State :=
  Stele.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
    (UInt256.sub (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩) value)

def burnBalanceState (evm : State) (sender : AccountAddress) (value : UInt256) : State :=
  burnSupplyState (balanceDebitState evm sender value) value

theorem balanceBurnTail (imms : Store) (evm : State) (sender : AccountAddress)
    (value balance : UInt256) :
    ExecBlock config (balanceUpdateReadFrame imms sender (AccountAddress.ofNat 0) value balance)
      evm balanceUpdateTail
      (.ok (balanceUpdateReadFrame imms sender (AccountAddress.ofNat 0) value balance)
        (burnSupplyState evm value)) := by
  have hc : evalExpr? config
      (balanceUpdateReadFrame imms sender (AccountAddress.ofNat 0) value balance) evm
      (.binary .eq (.var "to") (.cast (.intLit 0) (.elem .address))) = .ok (.bool true) := by
    have h := evalExpr_addressEq (cfg := config)
      (stele := balanceUpdateReadFrame imms sender (AccountAddress.ofNat 0) value balance) (evm := evm)
      (a := AccountAddress.ofNat 0) (b := AccountAddress.ofNat 0)
      (lhs := .var "to") (rhs := .cast (.intLit 0) (.elem .address))
      (by simp [evalExpr?, balanceUpdateReadFrame, balanceUpdateFrame,
        Std.HashMap.getElem_insert, EvalResult.ofOption])
      (evalAddressLiteral _ _ _ (AccountAddress.ofNat 0))
    simpa only [decide_true] using h
  refine ExecBlock.consNormal
    (stele' := balanceUpdateReadFrame imms sender (AccountAddress.ofNat 0) value balance)
    (evm' := burnSupplyState evm value) (ExecStmt.iteTrue hc ?_) ?_
  · apply ExecBlock.consNormal (ExecStmt.assign (value := uint256Value
      (UInt256.sub (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩) value)) ?_ ?_) ExecBlock.nil
    · apply wrappingSubSource
      · exact evalStorage_totalSupply evm _ imms (by simp [balanceUpdateFrame])
      · simp [evalExpr?, balanceUpdateReadFrame, balanceUpdateFrame,
          Std.HashMap.getElem_insert, EvalResult.ofOption]
    · exact assignStorageRef_storage_scalar_value (er := ⟨"_totalSupply", []⟩)
        (ty := .elem (.int (.uint ⟨256, by decide⟩)))
        (by simp [balanceUpdateReadFrame, balanceUpdateFrame])
        (by simp [evalStorageRef, evalStorageRefSteps, bind, EvalResult.bind, pure])
        rfl rfl rfl (.inl ⟨_, rfl⟩) (storageLocStore_uint256 evm ⟨2⟩ _)
  · apply ExecBlock.consNormal (ExecStmt.emit
      (vals := [.address sender, .address (AccountAddress.ofNat 0), uint256Value value]) ?_) ExecBlock.nil
    simp [evalExprs?, evalExpr?, balanceUpdateReadFrame, balanceUpdateFrame,
      Std.HashMap.getElem_insert, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem balanceBurnBody (imms : Store) (evm : State) (sender : AccountAddress)
    (value : UInt256) (hfrom : sender ≠ AccountAddress.ofNat 0)
    (hbal : value.toNat ≤ (balanceWord evm sender).toNat) :
    ExecFuncBody config (balanceUpdateFrame imms sender (AccountAddress.ofNat 0) value) evm
      balanceUpdateFunction.body
      (.returned (balanceUpdateReadFrame imms sender (AccountAddress.ofNat 0) value
        (balanceWord evm sender)) (burnBalanceState evm sender value) none) := by
  have hfrom' : sender ≠ ⟨0, by decide⟩ := hfrom
  apply ExecFuncBody.execBlockOK
  rw [balanceUpdateFunction_body]
  refine ExecBlock.consNormal
    (stele' := balanceUpdateReadFrame imms sender (AccountAddress.ofNat 0) value (balanceWord evm sender))
    (evm' := balanceDebitState evm sender value)
    (ExecStmt.iteFalse (by rw [balanceUpdateFromCondition, decide_eq_false hfrom']) ?_) ?_
  · apply (balanceUpdateRead imms evm sender (AccountAddress.ofNat 0) value).run
    apply ExecBlock.consNormal (ExecStmt.requireTrue
      (by rw [balanceUpdateEnough, decide_eq_true hbal]))
    exact ExecBlock.consNormal (balanceUpdateDebit imms evm sender (AccountAddress.ofNat 0) value) ExecBlock.nil
  · exact balanceBurnTail imms _ sender value _

end Benchmarks.Morpho.MetaMorphoV1_1
