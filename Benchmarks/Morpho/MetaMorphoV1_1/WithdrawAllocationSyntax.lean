import Benchmarks.Morpho.MetaMorphoV1_1.DepositAllocationSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawViewsAllocationSyntax

/-! Compiler allocation checks through accrued supply balance and actual withdrawals. -/

open Stele ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def allocatedAccruedSupplyBalanceFunction : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[17]!
  { source with
    name := "__solcAccruedSupplyBalance"
    params := source.params ++ [{ name := cursorName, ty := cursorType }]
    returnType := [returnValueType source.returnType, cursorType]
    body := reserveBytes 192 :: allocationBody (fun name ↦
      if name == "MorphoLib_supplyShares" then some allocatedSupplySharesFunction.name else none)
      (fun name ↦ if name == "market" then 384 else 0) source.body }

def allocatedWithdrawMorphoFunction : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[64]!
  { source with
    name := "__solcWithdrawMorpho"
    params := source.params ++ [{ name := cursorName, ty := cursorType }]
    returnType := [.tuple [], cursorType]
    body := allocationBody (fun name ↦
      if name == "_marketParams" then some allocatedMarketParamsFunction.name
      else if name == "_accruedSupplyBalance" then some allocatedAccruedSupplyBalanceFunction.name
      else if name == "_withdrawable" then some allocatedWithdrawableFunction.name
      else none) (fun name ↦ if name == "withdraw" then 64 else 0) source.body ++
        [.return [.tupleLit [], .var cursorName]] }

def allocatedERC4626WithdrawFunction : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[65]!
  { source with
    name := "__solcERC4626Withdraw"
    params := source.params ++ [{ name := cursorName, ty := cursorType }]
    returnType := [cursorType]
    body := source.body.take 2 ++
      [.internalCall allocatedSafeTransferFunction.name
        [.immutable "_asset", .var "receiver", .var "assets", .var cursorName] cursorName] ++
      source.body.drop 3 ++ [.return [.var cursorName]] }

def allocatedWithdrawFunction : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[28]!
  { source with
    name := "__solcWithdraw"
    params := source.params ++ [{ name := cursorName, ty := cursorType }]
    returnType := [cursorType]
    body := source.body.take 2 ++
      cursorCall allocatedWithdrawMorphoFunction.name [.var "assets"] "__c2" ++
      [.internalCall allocatedERC4626WithdrawFunction.name
        [.var "caller", .var "receiver", .var "owner", .var "assets", .var "shares",
          .var cursorName] cursorName,
       .return [.var cursorName]] }

def withdrawCursorStatement : Stmt → Stmt
  | .internalCall "_accrueInterest" args _ =>
      .internalCall allocatedAccrueInterestFunction.name (args ++ [.var cursorName]) cursorName
  | .internalCall "_withdraw" args result =>
      .internalCall allocatedWithdrawFunction.name (args ++ [.var cursorName]) result
  | stmt => stmt

def allocatedWithdrawTransition : TransitionDecl :=
  let source := Syntax.contractSyntax.transitions[54]!
  { source with
    body := source.body.take 3 ++ [.letDecl cursorName (some cursorType) (.intLit 128)] ++
      (source.body.drop 3).map withdrawCursorStatement }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
