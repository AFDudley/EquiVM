import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoSyntax

/-! Source execution of the supply loop's try/catch, allocation, and asset subtraction. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

structure SupplyCallLocals (frame : Frame) (morpho : AccountAddress) (p : MarketParamsData)
    (ptr assets amount : UInt256) : Prop where
  contract : frame.contract = contract
  target : frame.locals.get? "morphoTarget" = some (.address morpho)
  params : frame.locals.get? "marketParams" = some p.value
  cursor : frame.locals.get? cursorName = some (uint256Value ptr)
  assets : frame.locals.get? "assets" = some (uint256Value assets)
  amount : frame.locals.get? "toSupply" = some (uint256Value amount)

def supplyCallDecodedFrame (frame : Frame) (out : ByteArray) : Frame :=
  { frame with locals := frame.locals.insert "__ret" (.tuple
      [uint256Value (calldataWord out 0), uint256Value (calldataWord out 32)]) }

def supplyCallReservedFrame (frame : Frame) (ptr : UInt256) (out : ByteArray) : Frame :=
  { supplyCallDecodedFrame frame out with locals :=
      (supplyCallDecodedFrame frame out).locals.insert cursorName (uint256Value (nextCursor ptr ⟨64⟩)) }

def supplyCallSuccessFrame (frame : Frame) (ptr assets amount : UInt256) (out : ByteArray) : Frame :=
  { supplyCallReservedFrame frame ptr out with locals :=
      (supplyCallReservedFrame frame ptr out).locals.insert "assets" (uint256Value (UInt256.sub assets amount)) }

def supplyCallFailureFrame (frame : Frame) (out : ByteArray) : Frame :=
  { frame with locals := frame.locals.insert "__err" (.bytes out) }

theorem supplyCallArgs {frame : Frame} {evm : State} {morpho : AccountAddress}
    {p : MarketParamsData} {ptr assets amount : UInt256}
    (h : SupplyCallLocals frame morpho p ptr assets amount) :
    evalExprs? config frame evm
      [.var "marketParams", .var "toSupply", .intLit 0, .env .this, .newBytes (.intLit 0)] =
      .ok [p.value, uint256Value amount, uint256Value ⟨0⟩,
        .address evm.executionEnv.codeOwner, .bytes ByteArray.empty] := by
  have hn : evalExpr? config frame evm (.newBytes (.intLit 0)) = .ok (.bytes ByteArray.empty) := by
    simp only [evalExpr?, pure, bind, EvalResult.bind]
    rfl
  simp only [evalExprs?, hn, evalExpr?, h.params, h.amount, EvalResult.ofOption,
    envValue, pure, bind, EvalResult.bind]
  rfl

theorem supplyCallDecodedCursor {frame : Frame} {evm : State} {ptr : UInt256} (out : ByteArray)
    (hptr : frame.locals.get? cursorName = some (uint256Value ptr)) :
    evalExpr? config (supplyCallDecodedFrame frame out) evm (.var cursorName) =
      .ok (uint256Value ptr) := by
  simp only [evalExpr?, supplyCallDecodedFrame,
    store_get_ne _ _ (by decide : ("__ret" == cursorName) = false), hptr, EvalResult.ofOption]

theorem supplyCallSourceFailure {frame : Frame} {evm evm' : State} {morpho : AccountAddress}
    {p : MarketParamsData} {ptr assets amount : UInt256} {out : ByteArray}
    (h : SupplyCallLocals frame morpho p ptr assets amount)
    (hcall : typedCallViaEVM config evm morpho "supply" 0
      [p.value, uint256Value amount, uint256Value ⟨0⟩, .address evm.executionEnv.codeOwner,
        .bytes ByteArray.empty] (false, evm', out)) :
    ExecStmt config frame evm supplyMorphoCall (.ok (supplyCallFailureFrame frame out) evm') := by
  exact ExecStmt.checkedCallFail (target := morpho) (sendVal := 0) (evm' := evm') (out := out)
    (by simp only [evalExpr?, h.target, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]) (supplyCallArgs h) (by rw [show EVM.address (morpho : Nat) = morpho from evm_address_of_address_toNat morpho]; exact hcall) ExecBlock.nil

theorem supplyCallSourceReverts {frame : Frame} {evm evm' : State} {morpho : AccountAddress}
    {p : MarketParamsData} {ptr assets amount : UInt256} {out : ByteArray}
    (h : SupplyCallLocals frame morpho p ptr assets amount)
    (hcall : typedCallViaEVM config evm morpho "supply" 0
      [p.value, uint256Value amount, uint256Value ⟨0⟩, .address evm.executionEnv.codeOwner,
        .bytes ByteArray.empty] (true, evm', out))
    (hhi : out.size < 2 ^ 255) (hbad : ¬ (64 ≤ out.size ∧ allocationFits ptr ⟨64⟩)) :
    ExecStmt config frame evm supplyMorphoCall .reverted := by
  by_cases hl : 64 ≤ out.size
  · apply ExecStmt.checkedCallSuccess (target := morpho) (sendVal := 0) (evm' := evm') (out := out)
      (by simp only [evalExpr?, h.target, EvalResult.ofOption])
      (by simp only [evalExpr?, pure]) (supplyCallArgs h) (by rw [show EVM.address (morpho : Nat) = morpho from evm_address_of_address_toNat morpho]; exact hcall)
      (by rw [morphoSupplyDecode hhi, if_pos hl])
    exact ExecBlock.consRevert (allocateCallReverts cursorName
      (by change lookupCallable? frame.contract _ = _; rw [h.contract]; exact allocateFunction_lookup)
      (supplyCallDecodedCursor out h.cursor) (by simp only [evalExpr?, pure]; rfl)
      (fun hf ↦ hbad ⟨hl, hf⟩))
  · exact ExecStmt.checkedCallReturnDecodeRevert (target := morpho) (sendVal := 0) (evm' := evm') (out := out)
      (by simp only [evalExpr?, h.target, EvalResult.ofOption])
      (by simp only [evalExpr?, pure]) (supplyCallArgs h) (by rw [show EVM.address (morpho : Nat) = morpho from evm_address_of_address_toNat morpho]; exact hcall)
      (by rw [morphoSupplyDecode hhi, if_neg hl])

theorem supplyCallReservedFrame_preserves (frame : Frame) (ptr : UInt256) (out : ByteArray)
    (name : Ident) (hr : ("__ret" == name) = false) (hc : (cursorName == name) = false) :
    (supplyCallReservedFrame frame ptr out).locals.get? name = frame.locals.get? name := by
  rw [supplyCallReservedFrame, store_get_ne _ _ hc, supplyCallDecodedFrame, store_get_ne _ _ hr]

theorem supplyCallSourceSuccess {frame : Frame} {evm evm' : State} {morpho : AccountAddress}
    {p : MarketParamsData} {ptr assets amount : UInt256} {out : ByteArray}
    (h : SupplyCallLocals frame morpho p ptr assets amount)
    (hcall : typedCallViaEVM config evm morpho "supply" 0
      [p.value, uint256Value amount, uint256Value ⟨0⟩, .address evm.executionEnv.codeOwner,
        .bytes ByteArray.empty] (true, evm', out))
    (hhi : out.size < 2 ^ 255) (hlong : 64 ≤ out.size) (hfit : allocationFits ptr ⟨64⟩)
    (hsub : amount.toNat ≤ assets.toNat) :
    ExecStmt config frame evm supplyMorphoCall
      (.ok (supplyCallSuccessFrame frame ptr assets amount out) evm') := by
  apply ExecStmt.checkedCallSuccess (target := morpho) (sendVal := 0) (evm' := evm') (out := out)
    (by simp only [evalExpr?, h.target, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]) (supplyCallArgs h) (by rw [show EVM.address (morpho : Nat) = morpho from evm_address_of_address_toNat morpho]; exact hcall)
    (by rw [morphoSupplyDecode hhi, if_pos hlong])
  apply ExecBlock.consNormal (allocateCallReturns cursorName
    (by change lookupCallable? frame.contract _ = _; rw [h.contract]; exact allocateFunction_lookup)
    (supplyCallDecodedCursor out h.cursor) (by simp only [evalExpr?, pure]; rfl) hfit)
  change ExecBlock config (supplyCallReservedFrame frame ptr out) evm' _ _
  have ha : (supplyCallReservedFrame frame ptr out).locals.get? "assets" =
      some (uint256Value assets) := by
    rw [supplyCallReservedFrame_preserves _ _ _ _ (by decide) (by decide)]
    exact h.assets
  have ht : (supplyCallReservedFrame frame ptr out).locals.get? "toSupply" =
      some (uint256Value amount) := by
    rw [supplyCallReservedFrame_preserves _ _ _ _ (by decide) (by decide)]
    exact h.amount
  apply ExecBlock.consNormal (ExecStmt.assign (evalExpr_uint256_sub ?_ ?_ hsub) ?_) ExecBlock.nil
  · simp only [evalExpr?, ha, EvalResult.ofOption]
  · simp only [evalExpr?, ht, EvalResult.ofOption]
  · simp only [assignStorageRef?, ha, updateLocalPath?, bind, EvalResult.bind, pure]
    rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
