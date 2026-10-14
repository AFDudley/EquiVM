import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoExternalSource
import Benchmarks.Morpho.MetaMorphoV1_1.AllocatedReaderCalls
import Benchmarks.Morpho.MetaMorphoV1_1.CursorCallSource

/-! Source prefix of the allocated accrued-supply-balance helper. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def accruedSupplyInitialStatements : List Stmt :=
  reserveBytes 192 :: (Syntax.contractSyntax.functions[17]!).body.take 4

def accruedSupplyGuard : Stmt := (Syntax.contractSyntax.functions[17]!).body[4]!
def accruedSupplyAccrue : Stmt := (Syntax.contractSyntax.functions[17]!).body[5]!
def accruedSupplyMarket : List Stmt :=
  [.externalCall (.var "morphoTarget") "market" (.intLit 0) [.var "id"] "__c1" false,
   reserveBytes 384, .assign .localVar ⟨"market", []⟩ (.var "__c1")]
def accruedSupplyShares : List Stmt :=
  cursorCall allocatedSupplySharesFunction.name
    [.immutable "MORPHO", .var "id", .env .this] "__c2"
def accruedSupplyTail : List Stmt :=
  [.assign .localVar ⟨"shares", []⟩ (.var "__c2"),
   .internalCall "SharesMathLib_toAssetsDown"
     [.var "shares", .field (.var "market") "totalSupplyAssets",
       .field (.var "market") "totalSupplyShares"] "__c3",
   .assign .localVar ⟨"assets", []⟩ (.var "__c3"),
   .return [.tupleLit [.var "assets", .var "shares", .var "market"], .var cursorName]]

set_option maxRecDepth 2000 in
theorem allocatedAccruedSupplyBalanceFunction_body :
    allocatedAccruedSupplyBalanceFunction.body = accruedSupplyInitialStatements ++
      accruedSupplyGuard :: accruedSupplyAccrue :: accruedSupplyMarket ++
        accruedSupplyShares ++ accruedSupplyTail := by decide +kernel

set_option maxRecDepth 2000 in
theorem allocatedAccruedSupplyBalanceFunction_lookup :
    lookupCallable? contract allocatedAccruedSupplyBalanceFunction.name =
      some allocatedAccruedSupplyBalanceFunction.toCallable := by rfl

def accruedSupplyFrame (imms : Store) (p : MarketParamsData) (id ptr : UInt256) : Frame :=
  { contract := contract
    locals := (((∅ : Store).insert cursorName (uint256Value ptr)).insert
      "id" (wordBytes32Value id)).insert "marketParams" p.value
    immutables := imms }

def accruedSupplyZeroMarket : Value :=
  .struct "Market" [("totalSupplyAssets", .int 0), ("totalSupplyShares", .int 0),
    ("totalBorrowAssets", .int 0), ("totalBorrowShares", .int 0),
    ("lastUpdate", .int 0), ("fee", .int 0)]

def accruedSupplyGuardFrame (imms : Store) (morpho : AccountAddress)
    (p : MarketParamsData) (id ptr : UInt256) : Frame :=
  { accruedSupplyFrame imms p id ptr with
    locals := (((((accruedSupplyFrame imms p id ptr).locals.insert
      cursorName (uint256Value (nextCursor ptr ⟨192⟩))).insert
      "morphoTarget" (.address morpho)).insert "assets" (.int 0)).insert
      "shares" (.int 0)).insert "market" accruedSupplyZeroMarket }

def accruedSupplyAccruedFrame (frame : Frame) : Frame :=
  { frame with locals := frame.locals.insert "__c0" .unit }

def accruedSupplyDecodedFrame (frame : Frame) (out : ByteArray) : Frame :=
  { frame with locals := frame.locals.insert "__c1" (marketValue out) }

def accruedSupplyMarketFrame (frame : Frame) (ptr : UInt256) (out : ByteArray) : Frame :=
  { frame with locals := (((accruedSupplyDecodedFrame frame out).locals.insert
    cursorName (uint256Value (nextCursor ptr ⟨384⟩))).insert "market" (marketValue out)) }

theorem accruedSupplyInitialSourceReverts (evm : State) (imms : Store)
    (p : MarketParamsData) (id ptr : UInt256) (hbad : ¬ allocationFits ptr ⟨192⟩)
    (tail : List Stmt) :
    ExecBlock config (accruedSupplyFrame imms p id ptr) evm
      (accruedSupplyInitialStatements ++ tail) .reverted := by
  exact ExecBlock.consRevert (allocateCallReverts cursorName allocateFunction_lookup
    (by simp [evalExpr?, accruedSupplyFrame, cursorName, Std.HashMap.getElem_insert,
      EvalResult.ofOption]) (by simp only [evalExpr?, pure]; rfl) hbad)

theorem accruedSupplyInitialSource (evm : State) (v : MetaMorphoV1_1Immutables)
    (p : MarketParamsData) (id ptr : UInt256) (hfit : allocationFits ptr ⟨192⟩)
    (tail : List Stmt) :
    ABlock config evm (accruedSupplyFrame (immStore v) p id ptr)
      (accruedSupplyInitialStatements ++ tail)
      (accruedSupplyGuardFrame (immStore v) v.MORPHO p id ptr) tail := by
  constructor
  intro result htail
  apply ExecBlock.consNormal (allocateCallReturns cursorName allocateFunction_lookup
    (by simp [evalExpr?, accruedSupplyFrame, cursorName, Std.HashMap.getElem_insert,
      EvalResult.ofOption]) (by simp only [evalExpr?, pure]; rfl) hfit)
  apply ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_MORPHO _ _ _ _ _))
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure]))
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure]))
  exact ExecBlock.consNormal (ExecStmt.letDecl (value := accruedSupplyZeroMarket) (by
    simp [evalExpr?, evalStructFields?, pure, bind, EvalResult.bind,
      accruedSupplyZeroMarket])) htail

theorem accruedSupplyAccrueSuccess {frame : Frame} {evm evm' : State} {morpho : AccountAddress}
    {p : MarketParamsData} {out : ByteArray}
    (hm : frame.locals.get? "morphoTarget" = some (.address morpho))
    (hp : frame.locals.get? "marketParams" = some p.value)
    (hcall : typedCallViaEVM config evm morpho "accrueInterest" 0 [p.value] (true, evm', out)) :
    ExecStmt config frame evm accruedSupplyAccrue (.ok (accruedSupplyAccruedFrame frame) evm') :=
  ExecStmt.externalCallSuccess (target := morpho) (sendVal := 0)
    (evm' := evm') (out := out) (argVals := [p.value]) (value := [])
    (by simp only [evalExpr?, hm, EvalResult.ofOption]) (by simp only [evalExpr?, pure])
    (by simp only [evalExprs?, evalExpr?, hp, EvalResult.ofOption, pure, bind, EvalResult.bind])
    (by rw [show EVM.address (morpho : Nat) = morpho from evm_address_of_address_toNat morpho]; exact hcall)
    (morphoAccrueDecode out)

theorem accruedSupplyAccrueReverts {frame : Frame} {evm evm' : State} {morpho : AccountAddress}
    {p : MarketParamsData} {out : ByteArray}
    (hm : frame.locals.get? "morphoTarget" = some (.address morpho))
    (hp : frame.locals.get? "marketParams" = some p.value)
    (hcall : typedCallViaEVM config evm morpho "accrueInterest" 0 [p.value] (false, evm', out)) :
    ExecStmt config frame evm accruedSupplyAccrue .reverted :=
  ExecStmt.externalCallFailure (target := morpho) (sendVal := 0)
    (evm' := evm') (out := out) (argVals := [p.value])
    (by simp only [evalExpr?, hm, EvalResult.ofOption]) (by simp only [evalExpr?, pure])
    (by simp only [evalExprs?, evalExpr?, hp, EvalResult.ofOption, pure, bind, EvalResult.bind])
    (by rw [show EVM.address (morpho : Nat) = morpho from evm_address_of_address_toNat morpho]; exact hcall)

theorem accruedSupplyMarketSuccess {frame : Frame} {evm evm' : State} {morpho : AccountAddress}
    {id : UInt256} {out : ByteArray}
    (hm : frame.locals.get? "morphoTarget" = some (.address morpho))
    (hi : frame.locals.get? "id" = some (wordBytes32Value id))
    (hcall : typedCallViaEVM config evm morpho "market" 0 [wordBytes32Value id] (true, evm', out) false)
    (hc : MarketChecks out) (hh : out.size < 2 ^ 255) :
    ExecStmt config frame evm accruedSupplyMarket[0]!
      (.ok (accruedSupplyDecodedFrame frame out) evm') :=
  ExecStmt.externalCallSuccess (target := morpho) (sendVal := 0)
    (evm' := evm') (out := out) (argVals := [wordBytes32Value id]) (value := [marketValue out])
    (by simp only [evalExpr?, hm, EvalResult.ofOption]) (by simp only [evalExpr?, pure])
    (by simp only [evalExprs?, evalExpr?, hi, EvalResult.ofOption, pure, bind, EvalResult.bind])
    (by rw [show EVM.address (morpho : Nat) = morpho from evm_address_of_address_toNat morpho]; exact hcall)
    (by rw [marketDecode hh, if_pos hc])

theorem accruedSupplyMarketCursor {frame : Frame} {evm : State} {ptr : UInt256} (out : ByteArray)
    (hptr : frame.locals.get? cursorName = some (uint256Value ptr)) :
    evalExpr? config (accruedSupplyDecodedFrame frame out) evm (.var cursorName) =
      .ok (uint256Value ptr) := by
  simp only [evalExpr?, accruedSupplyDecodedFrame,
    store_get_ne _ _ (by decide : ("__c1" == cursorName) = false), hptr, EvalResult.ofOption]

theorem accruedSupplyMarketReverts {frame : Frame} {evm evm' : State} {morpho : AccountAddress}
    {id ptr : UInt256} {out : ByteArray} {ok : Bool}
    (hcontract : frame.contract = contract)
    (hm : frame.locals.get? "morphoTarget" = some (.address morpho))
    (hi : frame.locals.get? "id" = some (wordBytes32Value id))
    (hptr : frame.locals.get? cursorName = some (uint256Value ptr))
    (hcall : typedCallViaEVM config evm morpho "market" 0 [wordBytes32Value id] (ok, evm', out) false)
    (hh : out.size < 2 ^ 255) (hbad : ok = false ∨ ¬ (MarketChecks out ∧ allocationFits ptr ⟨384⟩))
    (tail : List Stmt) :
    ExecBlock config frame evm (accruedSupplyMarket ++ tail) .reverted := by
  cases ok with
  | false =>
      exact ExecBlock.consRevert (ExecStmt.externalCallFailure (target := morpho) (sendVal := 0)
        (evm' := evm') (out := out) (argVals := [wordBytes32Value id])
        (by simp only [evalExpr?, hm, EvalResult.ofOption]) (by simp only [evalExpr?, pure])
        (by simp only [evalExprs?, evalExpr?, hi, EvalResult.ofOption, pure, bind, EvalResult.bind])
        (by rw [show EVM.address (morpho : Nat) = morpho from evm_address_of_address_toNat morpho]; exact hcall))
  | true =>
      by_cases hc : MarketChecks out
      · apply ExecBlock.consNormal (accruedSupplyMarketSuccess hm hi hcall hc hh)
        exact ExecBlock.consRevert (allocateCallReverts cursorName
          (by change lookupCallable? frame.contract _ = _; rw [hcontract]; exact allocateFunction_lookup)
          (accruedSupplyMarketCursor out hptr) (by simp only [evalExpr?, pure]; rfl)
          (fun hf ↦ (hbad.resolve_left (by decide)) ⟨hc, hf⟩))
      · exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
          (target := morpho) (sendVal := 0)
          (evm' := evm') (out := out) (argVals := [wordBytes32Value id])
          (by simp only [evalExpr?, hm, EvalResult.ofOption]) (by simp only [evalExpr?, pure])
          (by simp only [evalExprs?, evalExpr?, hi, EvalResult.ofOption, pure, bind, EvalResult.bind])
          (by rw [show EVM.address (morpho : Nat) = morpho from evm_address_of_address_toNat morpho]; exact hcall)
          (by rw [marketDecode hh, if_neg hc]))

theorem accruedSupplyMarketPrefix {frame : Frame} {evm evm' : State} {morpho : AccountAddress}
    {id ptr : UInt256} {out : ByteArray} {old : Value}
    (hcontract : frame.contract = contract)
    (hm : frame.locals.get? "morphoTarget" = some (.address morpho))
    (hi : frame.locals.get? "id" = some (wordBytes32Value id))
    (hptr : frame.locals.get? cursorName = some (uint256Value ptr))
    (hold : frame.locals.get? "market" = some old)
    (hcall : typedCallViaEVM config evm morpho "market" 0 [wordBytes32Value id] (true, evm', out) false)
    (hc : MarketChecks out) (hh : out.size < 2 ^ 255) (hfit : allocationFits ptr ⟨384⟩)
    {tail : List Stmt} {result : ExecResult}
    (htail : ExecBlock config (accruedSupplyMarketFrame frame ptr out) evm' tail result) :
    ExecBlock config frame evm (accruedSupplyMarket ++ tail) result := by
  apply ExecBlock.consNormal (accruedSupplyMarketSuccess hm hi hcall hc hh)
  apply ExecBlock.consNormal (allocateCallReturns cursorName
    (by change lookupCallable? frame.contract _ = _; rw [hcontract]; exact allocateFunction_lookup)
    (accruedSupplyMarketCursor out hptr) (by simp only [evalExpr?, pure]; rfl) hfit)
  refine ExecBlock.consNormal (ExecStmt.assign ?_ (assignLocalValue (old := old) ?_)) htail
  · simp only [evalExpr?, accruedSupplyDecodedFrame,
      store_get_ne _ _ (by decide : (cursorName == "__c1") = false), store_get_self, EvalResult.ofOption]
  · simp only [accruedSupplyDecodedFrame,
      store_get_ne _ _ (by decide : (cursorName == "market") = false),
      store_get_ne _ _ (by decide : ("__c1" == "market") = false), hold]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
