import Benchmarks.Morpho.MetaMorphoV1_1.SafeTransferFromAllocationSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoAllocationSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.AccrueInterestAllocationSyntax

/-! Cursor propagation through token transfer, share minting, market supply, and deposit. -/

open Stele ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def allocatedERC4626DepositFunction : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[62]!
  { source with
    name := "__solcERC4626Deposit"
    params := source.params ++ [{ name := cursorName, ty := cursorType }]
    returnType := [cursorType]
    body := [.internalCall allocatedSafeTransferFromFunction.name
        [.immutable "_asset", .var "caller", .env .this, .var "assets", .var cursorName]
        cursorName] ++ source.body.drop 1 ++ [.return [.var cursorName]] }

def allocatedDepositFunction : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[26]!
  { source with
    name := "__solcDeposit"
    params := source.params ++ [{ name := cursorName, ty := cursorType }]
    returnType := [cursorType]
    body := [.internalCall allocatedERC4626DepositFunction.name
        [.var "caller", .var "receiver", .var "assets", .var "shares", .var cursorName]
        cursorName] ++ cursorCall allocatedSupplyMorphoFunction.name [.var "assets"] "__c1" ++
      source.body.drop 2 ++ [.return [.var cursorName]] }

def depositCursorStatement : Stmt → Stmt
  | .internalCall "_accrueInterest" args _ =>
      .internalCall allocatedAccrueInterestFunction.name (args ++ [.var cursorName]) cursorName
  | .internalCall "_deposit" args result =>
      .internalCall allocatedDepositFunction.name (args ++ [.var cursorName]) result
  | stmt => stmt

def allocatedDepositTransition : TransitionDecl :=
  let source := Syntax.contractSyntax.transitions[29]!
  { source with
    body := source.body.take 3 ++ [.letDecl cursorName (some cursorType) (.intLit 128)] ++
      (source.body.drop 3).map depositCursorStatement }

def allocatedMintTransition : TransitionDecl :=
  let source := Syntax.contractSyntax.transitions[43]!
  { source with
    body := source.body.take 3 ++ [.letDecl cursorName (some cursorType) (.intLit 128)] ++
      (source.body.drop 3).map depositCursorStatement }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
