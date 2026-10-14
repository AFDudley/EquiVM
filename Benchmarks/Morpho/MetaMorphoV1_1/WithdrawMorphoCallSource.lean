import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawMorphoSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoCallSource

/-! Source execution of the withdrawal loop's try/catch, allocation, and asset subtraction. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

structure WithdrawCallLocals (frame : Frame) (morpho : AccountAddress) (p : MarketParamsData)
    (ptr assets amount : UInt256) : Prop where
  contract : frame.contract = contract
  target : frame.locals.get? "morphoTarget" = some (.address morpho)
  params : frame.locals.get? "marketParams" = some p.value
  cursor : frame.locals.get? cursorName = some (uint256Value ptr)
  assets : frame.locals.get? "assets" = some (uint256Value assets)
  amount : frame.locals.get? "toWithdraw" = some (uint256Value amount)

theorem withdrawCallArgs {frame : Frame} {evm : State} {morpho : AccountAddress}
    {p : MarketParamsData} {ptr assets amount : UInt256}
    (h : WithdrawCallLocals frame morpho p ptr assets amount) :
    evalExprs? config frame evm
      [.var "marketParams", .var "toWithdraw", .intLit 0, .env .this, .env .this] =
      .ok [p.value, uint256Value amount, uint256Value ⟨0⟩,
        .address evm.executionEnv.codeOwner, .address evm.executionEnv.codeOwner] := by
  simp only [evalExprs?, evalExpr?, h.params, h.amount, EvalResult.ofOption,
    envValue, pure, bind, EvalResult.bind]
  rfl

theorem withdrawCallSourceFailure {frame : Frame} {evm evm' : State} {morpho : AccountAddress}
    {p : MarketParamsData} {ptr assets amount : UInt256} {out : ByteArray}
    (h : WithdrawCallLocals frame morpho p ptr assets amount)
    (hcall : typedCallViaEVM config evm morpho "withdraw" 0
      [p.value, uint256Value amount, uint256Value ⟨0⟩, .address evm.executionEnv.codeOwner,
        .address evm.executionEnv.codeOwner] (false, evm', out)) :
    ExecStmt config frame evm withdrawMorphoCall (.ok (supplyCallFailureFrame frame out) evm') := by
  exact ExecStmt.checkedCallFail (target := morpho) (sendVal := 0) (evm' := evm') (out := out)
    (by simp only [evalExpr?, h.target, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]) (withdrawCallArgs h) (by rw [show EVM.address (morpho : Nat) = morpho from evm_address_of_address_toNat morpho]; exact hcall) ExecBlock.nil

theorem withdrawCallSourceReverts {frame : Frame} {evm evm' : State} {morpho : AccountAddress}
    {p : MarketParamsData} {ptr assets amount : UInt256} {out : ByteArray}
    (h : WithdrawCallLocals frame morpho p ptr assets amount)
    (hcall : typedCallViaEVM config evm morpho "withdraw" 0
      [p.value, uint256Value amount, uint256Value ⟨0⟩, .address evm.executionEnv.codeOwner,
        .address evm.executionEnv.codeOwner] (true, evm', out))
    (hhi : out.size < 2 ^ 255) (hbad : ¬ (64 ≤ out.size ∧ allocationFits ptr ⟨64⟩)) :
    ExecStmt config frame evm withdrawMorphoCall .reverted := by
  by_cases hl : 64 ≤ out.size
  · apply ExecStmt.checkedCallSuccess (target := morpho) (sendVal := 0) (evm' := evm') (out := out)
      (by simp only [evalExpr?, h.target, EvalResult.ofOption])
      (by simp only [evalExpr?, pure]) (withdrawCallArgs h) (by rw [show EVM.address (morpho : Nat) = morpho from evm_address_of_address_toNat morpho]; exact hcall)
      (by rw [morphoWithdrawDecode hhi, if_pos hl])
    exact ExecBlock.consRevert (allocateCallReverts cursorName
      (by change lookupCallable? frame.contract _ = _; rw [h.contract]; exact allocateFunction_lookup)
      (supplyCallDecodedCursor out h.cursor) (by simp only [evalExpr?, pure]; rfl)
      (fun hf ↦ hbad ⟨hl, hf⟩))
  · exact ExecStmt.checkedCallReturnDecodeRevert (target := morpho) (sendVal := 0) (evm' := evm') (out := out)
      (by simp only [evalExpr?, h.target, EvalResult.ofOption])
      (by simp only [evalExpr?, pure]) (withdrawCallArgs h) (by rw [show EVM.address (morpho : Nat) = morpho from evm_address_of_address_toNat morpho]; exact hcall)
      (by rw [morphoWithdrawDecode hhi, if_neg hl])

theorem withdrawCallSourceSuccess {frame : Frame} {evm evm' : State} {morpho : AccountAddress}
    {p : MarketParamsData} {ptr assets amount : UInt256} {out : ByteArray}
    (h : WithdrawCallLocals frame morpho p ptr assets amount)
    (hcall : typedCallViaEVM config evm morpho "withdraw" 0
      [p.value, uint256Value amount, uint256Value ⟨0⟩, .address evm.executionEnv.codeOwner,
        .address evm.executionEnv.codeOwner] (true, evm', out))
    (hhi : out.size < 2 ^ 255) (hlong : 64 ≤ out.size) (hfit : allocationFits ptr ⟨64⟩)
    (hsub : amount.toNat ≤ assets.toNat) :
    ExecStmt config frame evm withdrawMorphoCall
      (.ok (supplyCallSuccessFrame frame ptr assets amount out) evm') := by
  apply ExecStmt.checkedCallSuccess (target := morpho) (sendVal := 0) (evm' := evm') (out := out)
    (by simp only [evalExpr?, h.target, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]) (withdrawCallArgs h) (by rw [show EVM.address (morpho : Nat) = morpho from evm_address_of_address_toNat morpho]; exact hcall)
    (by rw [morphoWithdrawDecode hhi, if_pos hlong])
  apply ExecBlock.consNormal (allocateCallReturns cursorName
    (by change lookupCallable? frame.contract _ = _; rw [h.contract]; exact allocateFunction_lookup)
    (supplyCallDecodedCursor out h.cursor) (by simp only [evalExpr?, pure]; rfl) hfit)
  change ExecBlock config (supplyCallReservedFrame frame ptr out) evm' _ _
  have ha : (supplyCallReservedFrame frame ptr out).locals.get? "assets" =
      some (uint256Value assets) := by
    rw [supplyCallReservedFrame_preserves _ _ _ _ (by decide) (by decide)]
    exact h.assets
  have ht : (supplyCallReservedFrame frame ptr out).locals.get? "toWithdraw" =
      some (uint256Value amount) := by
    rw [supplyCallReservedFrame_preserves _ _ _ _ (by decide) (by decide)]
    exact h.amount
  apply ExecBlock.consNormal (ExecStmt.assign (evalExpr_uint256_sub ?_ ?_ hsub) ?_) ExecBlock.nil
  · simp only [evalExpr?, ha, EvalResult.ofOption]
  · simp only [evalExpr?, ht, EvalResult.ofOption]
  · simp only [assignStorageRef?, ha, updateLocalPath?, bind, EvalResult.bind, pure]
    rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
