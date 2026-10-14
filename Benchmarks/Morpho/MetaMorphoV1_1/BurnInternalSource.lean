import Benchmarks.Morpho.MetaMorphoV1_1.BurnSupplySource

/-! The sender guard and internal update call for ERC20 burning. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def burnInternalFunction : FunctionDecl := contract.functions[87]!

def burnInternalFrame (imms : Store) (sender : AccountAddress) (value : UInt256) : Frame :=
  ⟨contract,
    ((∅ : Store).insert "value" (uint256Value value)).insert "account" (.address sender), imms⟩

def burnAllowed (evm : State) (sender : AccountAddress) (value : UInt256) : Prop :=
  sender ≠ AccountAddress.ofNat 0 ∧ value.toNat ≤ (balanceWord evm sender).toNat

def burnInternalTail : List Stmt :=
  [.internalCall "_update" [.var "account", .cast (.intLit 0) (.elem .address), .var "value"]
    "__c0"]

theorem burnInternalFunction_body :
    burnInternalFunction.body =
      [.require (.binary .ne (.var "account") (.cast (.intLit 0) (.elem .address)))] ++
      burnInternalTail := by decide +kernel

theorem burnAccountCondition (imms : Store) (evm : State)
    (sender : AccountAddress) (value : UInt256) :
    evalExpr? config (burnInternalFrame imms sender value) evm
      (.binary .ne (.var "account") (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool (decide (sender ≠ AccountAddress.ofNat 0))) := by
  apply evalExpr_addressNe
  · simp only [evalExpr?, burnInternalFrame, store_get_self, EvalResult.ofOption]
  · exact evalAddressLiteral _ _ _ (AccountAddress.ofNat 0)

theorem burnUpdateArgs (imms : Store) (evm : State)
    (sender : AccountAddress) (value : UInt256) :
    evalExprs? config (burnInternalFrame imms sender value) evm
      [.var "account", .cast (.intLit 0) (.elem .address), .var "value"] =
      .ok [.address sender, .address (AccountAddress.ofNat 0), uint256Value value] := by
  have hz : evalExpr? config (burnInternalFrame imms sender value) evm
      (.cast (.intLit 0) (.elem .address)) = .ok (.address (AccountAddress.ofNat 0)) :=
    evalAddressLiteral _ _ _ (AccountAddress.ofNat 0)
  have ha : evalExpr? config (burnInternalFrame imms sender value) evm (.var "account") =
      .ok (.address sender) := by
    simp only [evalExpr?, burnInternalFrame, store_get_self, EvalResult.ofOption]
  have hv : evalExpr? config (burnInternalFrame imms sender value) evm (.var "value") =
      .ok (uint256Value value) := by
    simp [evalExpr?, burnInternalFrame, Std.HashMap.getElem_insert, EvalResult.ofOption]
  simp only [evalExprs?, hz, ha, hv, pure, bind, EvalResult.bind]

theorem burnInternalPrefix (imms : Store) (evm : State)
    (sender : AccountAddress) (value : UInt256) (hto : sender ≠ AccountAddress.ofNat 0) :
    ABlock config evm (burnInternalFrame imms sender value) burnInternalFunction.body
      (burnInternalFrame imms sender value) burnInternalTail := by
  rw [burnInternalFunction_body]
  exact ABlock.start.requireStep (by rw [burnAccountCondition, decide_eq_true hto])

theorem burnInternalBody (imms : Store) (evm : State)
    (sender : AccountAddress) (value : UInt256) (hgood : burnAllowed evm sender value) :
    ExecFuncBody config (burnInternalFrame imms sender value) evm burnInternalFunction.body
      (.returned { burnInternalFrame imms sender value with
        locals := (burnInternalFrame imms sender value).locals.insert "__c0" .unit }
        (burnBalanceState evm sender value) none) := by
  apply ExecFuncBody.execBlockOK
  apply (burnInternalPrefix imms evm sender value hgood.1).run
  exact ExecBlock.consNormal
    (internalCallFunctionReturn (callee := balanceUpdateFunction)
      (burnUpdateArgs imms evm sender value) rfl rfl
      (balanceBurnBody imms evm sender value hgood.1 hgood.2)) ExecBlock.nil

theorem burnInternalReverts (imms : Store) (evm : State)
    (sender : AccountAddress) (value : UInt256) (hbad : ¬ burnAllowed evm sender value) :
    ExecFuncBody config (burnInternalFrame imms sender value) evm burnInternalFunction.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  by_cases hto : sender ≠ AccountAddress.ofNat 0
  · apply (burnInternalPrefix imms evm sender value hto).run
    exact ExecBlock.consRevert (internalCallFunctionRevert (callee := balanceUpdateFunction)
      (burnUpdateArgs imms evm sender value) rfl rfl
      (balanceUpdateMoveReverts imms evm sender (AccountAddress.ofNat 0) value hto
        (fun hfit ↦ hbad ⟨hto, hfit⟩)))
  · rw [burnInternalFunction_body]
    exact ABlock.start.requireRevert (by rw [burnAccountCondition, decide_eq_false hto])

theorem burnCall {locals imms : Store} {evm : State} {sender : AccountAddress}
    {value : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address sender, uint256Value value])
    (hgood : burnAllowed evm sender value) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_burn" args ret)
      (.ok ⟨contract, locals.insert ret .unit, imms⟩ (burnBalanceState evm sender value)) :=
  internalCallFunctionReturn (callee := burnInternalFunction) hargs rfl rfl
    (burnInternalBody imms evm sender value hgood)

theorem burnCallReverts {locals imms : Store} {evm : State} {sender : AccountAddress}
    {value : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [.address sender, uint256Value value])
    (hbad : ¬ burnAllowed evm sender value) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_burn" args ret) .reverted :=
  internalCallFunctionRevert (callee := burnInternalFunction) hargs rfl rfl
    (burnInternalReverts imms evm sender value hbad)


end Benchmarks.Morpho.MetaMorphoV1_1
