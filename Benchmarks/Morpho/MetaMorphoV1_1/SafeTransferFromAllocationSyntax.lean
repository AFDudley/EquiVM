import Benchmarks.Morpho.MetaMorphoV1_1.EncodedOptionalCallSyntax

/-! The transferFrom helper carries its allocated request and returndata cursor. -/

open Stele ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def allocatedSafeTransferFromFunction : FunctionDecl :=
  { name := "__solcSafeTransferFrom"
    params := (Syntax.contractSyntax.functions[85]!).params ++
      [{ name := cursorName, ty := .elem (.int (.uint ⟨256, by decide⟩)) }]
    returnType := [.elem (.int (.uint ⟨256, by decide⟩))]
    body := encodedOptionalCallBody
      (.abiEncodeCall "transferFrom" [.var "from", .var "to", .var "value"]) ⟨132⟩ }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
