import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositAllocationSyntax

/-! Allocations in the market-supply loop, including successful try-call return buffers. -/

open Stele ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def allocatedSupplyMorphoFunction : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[63]!
  { source with
    name := "__solcSupplyMorpho"
    params := source.params ++ [{ name := cursorName, ty := cursorType }]
    returnType := [.tuple [], cursorType]
    body := allocationBody (fun name ↦
      if name == "_marketParams" then some allocatedMarketParamsFunction.name
      else if name == "MorphoLib_supplyShares" then some allocatedSupplySharesFunction.name
      else none)
      (fun name ↦ if name == "market" then 384 else if name == "supply" then 64 else 0)
      source.body ++ [.return [.tupleLit [], .var cursorName]] }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
