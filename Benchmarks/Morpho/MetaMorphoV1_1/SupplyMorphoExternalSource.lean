import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoSyntax
import Reasoning.ExternalCall

/-! Source execution of the supply loop's Morpho code guard, accrual, and market read. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def supplyAccruedFrame (frame : Frame) : Frame :=
  { frame with locals := frame.locals.insert "__c1" .unit }

def supplyMarketFrame (frame : Frame) (out : ByteArray) : Frame :=
  { frame with locals := frame.locals.insert "market" (marketValue out) }

def supplyMarketReservedFrame (frame : Frame) (ptr : UInt256) (out : ByteArray) : Frame :=
  { supplyMarketFrame frame out with locals :=
      (supplyMarketFrame frame out).locals.insert cursorName (uint256Value (nextCursor ptr ⟨384⟩)) }

theorem supplyMorphoCodeSource {frame : Frame} {evm : State} (v : MetaMorphoV1_1Immutables)
    (himms : frame.immutables = immStore v) :
    evalExpr? config frame evm (.binary .gt (.extCodeSize (.immutable "MORPHO")) (.intLit 0)) =
      .ok (.bool (decide (extCodeSizeWord evm.accountMap (UInt256.ofNat v.MORPHO.toNat) ≠ ⟨0⟩))) := by
  have hi : evalExpr? config frame evm (.immutable "MORPHO") = .ok (.address v.MORPHO) := by
    cases frame with
    | mk c locals imms =>
        dsimp only at himms
        subst imms
        exact evalImmutable_MORPHO _ _ _ _ _
  have ha : AccountAddress.ofUInt256 (UInt256.ofNat v.MORPHO.toNat) = v.MORPHO := by
    rw [accountAddress_ofUInt256_eq_ofNat_toNat]
    exact accountAddress_of_word_val _
  have he := extCodeSource (cfg := config) rfl (by rw [ha]; exact hi)
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  simp only [he, evalExpr?, bind, EvalResult.bind, pure, evalBinaryOpGtInt, gt_iff_lt,
    Int.ofNat_eq_natCast, Int.natCast_pos]
  congr 3
  exact propext ⟨fun hp hz ↦ by rw [hz] at hp; exact (Nat.lt_irrefl 0) hp,
    fun hn ↦ Nat.pos_of_ne_zero (fun hz ↦ hn (uint256_toNat_eq_zero hz))⟩

theorem supplyAccrueSourceReturns {frame : Frame} {evm evm' : State} {morpho : AccountAddress}
    {p : MarketParamsData} {out : ByteArray}
    (hm : frame.locals.get? "morphoTarget" = some (.address morpho))
    (hp : frame.locals.get? "marketParams" = some p.value)
    (hcall : typedCallViaEVM config evm morpho "accrueInterest" 0 [p.value] (true, evm', out)) :
    ExecStmt config frame evm supplyMorphoAccrual[1]! (.ok (supplyAccruedFrame frame) evm') := by
  exact ExecStmt.externalCallSuccess (target := morpho) (sendVal := 0)
    (evm' := evm') (out := out) (argVals := [p.value]) (value := [])
    (by simp only [evalExpr?, hm, EvalResult.ofOption]) (by simp only [evalExpr?, pure])
    (by simp only [evalExprs?, evalExpr?, hp, EvalResult.ofOption, pure, bind, EvalResult.bind])
    (by rw [show EVM.address (morpho : Nat) = morpho from evm_address_of_address_toNat morpho]; exact hcall)
    (morphoAccrueDecode out)

theorem supplyAccrueSourceReverts {frame : Frame} {evm evm' : State} {morpho : AccountAddress}
    {p : MarketParamsData} {out : ByteArray}
    (hm : frame.locals.get? "morphoTarget" = some (.address morpho))
    (hp : frame.locals.get? "marketParams" = some p.value)
    (hcall : typedCallViaEVM config evm morpho "accrueInterest" 0 [p.value] (false, evm', out)) :
    ExecStmt config frame evm supplyMorphoAccrual[1]! .reverted := by
  exact ExecStmt.externalCallFailure (target := morpho) (sendVal := 0) (evm' := evm') (out := out)
    (argVals := [p.value])
    (by simp only [evalExpr?, hm, EvalResult.ofOption]) (by simp only [evalExpr?, pure])
    (by simp only [evalExprs?, evalExpr?, hp, EvalResult.ofOption, pure, bind, EvalResult.bind])
    (by rw [show EVM.address (morpho : Nat) = morpho from evm_address_of_address_toNat morpho]; exact hcall)

theorem supplyMarketSourceSuccess {frame : Frame} {evm evm' : State} {morpho : AccountAddress}
    {id : UInt256} {out : ByteArray}
    (hm : frame.locals.get? "morphoTarget" = some (.address morpho))
    (hi : frame.locals.get? "id" = some (wordBytes32Value id))
    (hcall : typedCallViaEVM config evm morpho "market" 0 [wordBytes32Value id] (true, evm', out) false)
    (hc : MarketChecks out) (hh : out.size < 2 ^ 255) :
    ExecStmt config frame evm supplyMorphoMarket[0]! (.ok (supplyMarketFrame frame out) evm') := by
  exact ExecStmt.externalCallSuccess (target := morpho) (sendVal := 0)
    (evm' := evm') (out := out) (argVals := [wordBytes32Value id]) (value := [marketValue out])
    (by simp only [evalExpr?, hm, EvalResult.ofOption]) (by simp only [evalExpr?, pure])
    (by simp only [evalExprs?, evalExpr?, hi, EvalResult.ofOption, pure, bind, EvalResult.bind])
    (by rw [show EVM.address (morpho : Nat) = morpho from evm_address_of_address_toNat morpho]; exact hcall)
    (by rw [marketDecode hh, if_pos hc])

theorem supplyMarketSourceCursor {frame : Frame} {evm : State} {ptr : UInt256} (out : ByteArray)
    (hptr : frame.locals.get? cursorName = some (uint256Value ptr)) :
    evalExpr? config (supplyMarketFrame frame out) evm (.var cursorName) =
      .ok (uint256Value ptr) := by
  simp only [evalExpr?, supplyMarketFrame,
    store_get_ne _ _ (by decide : ("market" == cursorName) = false), hptr, EvalResult.ofOption]

theorem supplyMarketSourceReverts {frame : Frame} {evm evm' : State} {morpho : AccountAddress}
    {id ptr : UInt256} {out : ByteArray} {ok : Bool}
    (hcontract : frame.contract = contract)
    (hm : frame.locals.get? "morphoTarget" = some (.address morpho))
    (hi : frame.locals.get? "id" = some (wordBytes32Value id))
    (hptr : frame.locals.get? cursorName = some (uint256Value ptr))
    (hcall : typedCallViaEVM config evm morpho "market" 0 [wordBytes32Value id] (ok, evm', out) false)
    (hh : out.size < 2 ^ 255) (hbad : ok = false ∨ ¬ (MarketChecks out ∧ allocationFits ptr ⟨384⟩))
    (tail : List Stmt) :
    ExecBlock config frame evm (supplyMorphoMarket ++ tail) .reverted := by
  cases ok with
  | false =>
      exact ExecBlock.consRevert (ExecStmt.externalCallFailure (target := morpho) (sendVal := 0)
        (evm' := evm') (out := out) (argVals := [wordBytes32Value id])
        (by simp only [evalExpr?, hm, EvalResult.ofOption]) (by simp only [evalExpr?, pure])
        (by simp only [evalExprs?, evalExpr?, hi, EvalResult.ofOption, pure, bind, EvalResult.bind])
        (by rw [show EVM.address (morpho : Nat) = morpho from evm_address_of_address_toNat morpho]; exact hcall))
  | true =>
      by_cases hc : MarketChecks out
      · apply ExecBlock.consNormal (supplyMarketSourceSuccess hm hi hcall hc hh)
        exact ExecBlock.consRevert (allocateCallReverts cursorName
          (by change lookupCallable? frame.contract _ = _; rw [hcontract]; exact allocateFunction_lookup)
          (supplyMarketSourceCursor out hptr) (by simp only [evalExpr?, pure]; rfl)
          (fun hf ↦ (hbad.resolve_left (by decide)) ⟨hc, hf⟩))
      · exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
          (target := morpho) (sendVal := 0) (evm' := evm') (out := out)
          (argVals := [wordBytes32Value id])
          (by simp only [evalExpr?, hm, EvalResult.ofOption]) (by simp only [evalExpr?, pure])
          (by simp only [evalExprs?, evalExpr?, hi, EvalResult.ofOption, pure, bind, EvalResult.bind])
          (by rw [show EVM.address (morpho : Nat) = morpho from evm_address_of_address_toNat morpho]; exact hcall)
          (by rw [marketDecode hh, if_neg hc]))

theorem supplyMarketSourcePrefix {frame : Frame} {evm evm' : State} {morpho : AccountAddress}
    {id ptr : UInt256} {out : ByteArray}
    (hcontract : frame.contract = contract)
    (hm : frame.locals.get? "morphoTarget" = some (.address morpho))
    (hi : frame.locals.get? "id" = some (wordBytes32Value id))
    (hptr : frame.locals.get? cursorName = some (uint256Value ptr))
    (hcall : typedCallViaEVM config evm morpho "market" 0 [wordBytes32Value id] (true, evm', out) false)
    (hc : MarketChecks out) (hh : out.size < 2 ^ 255) (hfit : allocationFits ptr ⟨384⟩)
    {tail : List Stmt} {result : ExecResult}
    (htail : ExecBlock config (supplyMarketReservedFrame frame ptr out) evm' tail result) :
    ExecBlock config frame evm (supplyMorphoMarket ++ tail) result := by
  apply ExecBlock.consNormal (supplyMarketSourceSuccess hm hi hcall hc hh)
  exact ExecBlock.consNormal (allocateCallReturns cursorName
    (by change lookupCallable? frame.contract _ = _; rw [hcontract]; exact allocateFunction_lookup)
    (supplyMarketSourceCursor out hptr) (by simp only [evalExpr?, pure]; rfl) hfit) htail

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
