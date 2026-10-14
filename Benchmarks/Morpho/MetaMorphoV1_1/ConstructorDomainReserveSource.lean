import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDomainHashSource
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSource

/-! Source continuation through the checked domain reservation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] constructorNameHash constructorVersionHash
set_option autoImplicit false

def constructorDomainReservedFrame (frame : Frame) (ptr : UInt256) : Frame :=
  { constructorDomainConstantsFrame frame with
    locals := frame.locals.insert cursorName (uint256Value (nextCursor ptr ⟨192⟩)) }

theorem constructorDomainBodySplit : contract.ctor.body.drop 15 =
    constructorDomainConstantsBody ++ reserveBytes 192 :: contract.ctor.body.drop 21 := rfl

theorem constructorDomainReserveReverts {frame : Frame} {evm : State} {ptr : UInt256}
    (hcontract : frame.contract = contract)
    (hcursor : frame.locals.get? cursorName = some (uint256Value ptr))
    (hfit : ¬ allocationFits ptr ⟨192⟩) (rest : List Stmt) :
    ExecBlock config frame evm (constructorDomainConstantsBody ++ reserveBytes 192 :: rest)
      .reverted := by
  have hl : lookupCallable? frame.contract allocateFunction.name = some allocateFunction.toCallable := by
    rw [hcontract]
    exact allocateFunction_lookup
  have hl' : lookupCallable? (constructorDomainConstantsFrame frame).contract allocateFunction.name =
      some allocateFunction.toCallable := by
    simpa only [constructorDomainConstantsFrame] using hl
  have hcall := allocateCallReverts (frame := constructorDomainConstantsFrame frame)
    (cfg := config) (evm := evm) (ptrExpr := .var cursorName) (sizeExpr := .intLit 192)
    (ptr := ptr) (size := ⟨192⟩) cursorName hl'
    (by simp only [evalExpr?, constructorDomainConstantsFrame, hcursor, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]; rfl) hfit
  exact execBlock_append (constructorDomainConstantsSource (frame := frame) (evm := evm) hcontract)
    (ExecBlock.consRevert hcall)

theorem constructorDomainReservePrefix {frame : Frame} {evm : State} {ptr : UInt256}
    {rest : List Stmt} {result : ExecResult}
    (hcontract : frame.contract = contract)
    (hcursor : frame.locals.get? cursorName = some (uint256Value ptr))
    (hfit : allocationFits ptr ⟨192⟩)
    (htail : ExecBlock config (constructorDomainReservedFrame frame ptr) evm rest result) :
    ExecBlock config frame evm (constructorDomainConstantsBody ++ reserveBytes 192 :: rest)
      result := by
  have hl : lookupCallable? frame.contract allocateFunction.name = some allocateFunction.toCallable := by
    rw [hcontract]
    exact allocateFunction_lookup
  have hl' : lookupCallable? (constructorDomainConstantsFrame frame).contract allocateFunction.name =
      some allocateFunction.toCallable := by
    simpa only [constructorDomainConstantsFrame] using hl
  have hcall := allocateCallReturns (frame := constructorDomainConstantsFrame frame)
    (cfg := config) (evm := evm) (ptrExpr := .var cursorName) (sizeExpr := .intLit 192)
    (ptr := ptr) (size := ⟨192⟩) cursorName hl'
    (by simp only [evalExpr?, constructorDomainConstantsFrame, hcursor, EvalResult.ofOption])
    (by simp only [evalExpr?, pure]; rfl) hfit
  have hcall' : ExecStmt config (constructorDomainConstantsFrame frame) evm (reserveBytes 192)
      (.ok (constructorDomainReservedFrame frame ptr) evm) := by
    simpa only [constructorDomainReservedFrame, constructorDomainConstantsFrame] using hcall
  exact execBlock_append (constructorDomainConstantsSource (frame := frame) (evm := evm) hcontract)
    (ExecBlock.consNormal hcall' htail)

def constructorDomainCachedFrame (frame : Frame) (I : ExecutionEnv) : Frame :=
  { frame with
    locals := frame.locals.insert "domain" (wordBytes32Value (constructorDomainHash I))
    immutables := (frame.immutables.insert "_cachedDomainSeparator"
      (uint256Value (constructorDomainHash I))).insert "_cachedThis" (.address I.codeOwner) }

def constructorDomainCacheBody : List Stmt :=
  [.internalCall "_buildDomainSeparator" [] "domain",
   .setImmutable "_cachedDomainSeparator"
     (.cast (.var "domain") (.elem (.int (.uint ⟨256, by decide⟩)))),
   .setImmutable "_cachedThis" (.env .this)]

theorem constructorDomainCacheSource {frame : Frame} (evm : State)
    (hcontract : frame.contract = contract)
    (hname : frame.immutables.get? "_hashedName" = some (uint256Value constructorNameHash))
    (hversion : frame.immutables.get? "_hashedVersion" = some (uint256Value constructorVersionHash)) :
    ExecBlock config frame evm constructorDomainCacheBody
      (.ok (constructorDomainCachedFrame frame evm.executionEnv) evm) := by
  apply ExecBlock.consNormal (constructorBuildDomainCall evm "domain" hcontract hname hversion)
  apply ExecBlock.consNormal (ExecStmt.setImmutable
    (value := uint256Value (constructorDomainHash evm.executionEnv))
    (ty := .int (.uint ⟨256, by decide⟩)) ?_ ?_ (uint256Value_fits _))
  · apply ExecBlock.consNormal (ExecStmt.setImmutable
      (value := .address evm.executionEnv.codeOwner) (ty := .address) ?_ ?_ rfl) ExecBlock.nil
    · simp only [evalExpr?, pure]
      rfl
    · change immutableType? frame.contract "_cachedThis" = _
      rw [hcontract]
      rfl
  · exact evalExpr_bytes32ToUint (by simp only [evalExpr?, store_get_self, EvalResult.ofOption])
  · change immutableType? frame.contract "_cachedDomainSeparator" = _
    rw [hcontract]
    rfl

end Benchmarks.Morpho.MetaMorphoV1_1
