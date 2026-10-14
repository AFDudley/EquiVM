import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositAllocationSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.SafeTransferAllocationSyntax

/-! Request and raw-return allocation for the constructor's optional decimals query. -/

open Stele ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def allocatedTryGetAssetDecimalsFunction : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[44]!
  { source with
    name := "__solcTryGetAssetDecimals"
    params := source.params ++ [{ name := cursorName, ty := cursorType }]
    returnType := [returnValueType source.returnType, cursorType]
    body := [reserveBytes 36] ++ source.body.take 1 ++
      [.letDecl "returndata" none (.var "encodedDecimals"), reserveCallReturn] ++
      allocationBody (fun _ => none) (fun _ => 0) (source.body.drop 1) }

def constructorDecimalsCall : List Stmt :=
  cursorCall allocatedTryGetAssetDecimalsFunction.name [.var "assetAddress"] "decimalResult"

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
