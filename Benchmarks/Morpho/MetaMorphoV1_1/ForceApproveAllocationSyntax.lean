import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositAllocationSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.SafeTransferAllocationSyntax

/-! Request and return-buffer reservations for the constructor's force-approval call.

The first approval and the optional zero approval each allocate a 68-byte payload
with a length word. The final approval reuses the first payload. Every low-level
call reserves its nonempty raw return buffer before inspecting success or decoding.
-/

open Stele ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def allocatedOptionalReturnBoolFunction : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[75]!
  { source with
    name := "__solcCallOptionalReturnBool"
    params := source.params ++ [{ name := cursorName, ty := cursorType }]
    returnType := [returnValueType source.returnType, cursorType]
    body := source.body.take 1 ++ [reserveCallReturn] ++
      allocationBody (fun _ => none) (fun _ => 0) (source.body.drop 1) }

def allocatedForceApproveFunction : FunctionDecl :=
  let source := Syntax.contractSyntax.functions[46]!
  let fallback := match source.body[2]! with
    | .ite condition _ no =>
        .ite condition
          [reserveBytes 100,
           .internalCall allocatedOptionalReturnFunction.name
             [.var "token", .abiEncodeCall "approve" [.var "spender", .intLit 0],
              .var cursorName] cursorName,
           .internalCall allocatedOptionalReturnFunction.name
             [.var "token", .var "approvalCall", .var cursorName] cursorName] no
    | stmt => stmt
  { source with
    name := "__solcForceApprove"
    params := source.params ++ [{ name := cursorName, ty := cursorType }]
    returnType := [returnValueType source.returnType, cursorType]
    body := source.body.take 1 ++ [reserveBytes 100] ++
      cursorCall allocatedOptionalReturnBoolFunction.name
        [.var "token", .var "approvalCall"] "__c0" ++
      [fallback, .return [.tupleLit [], .var cursorName]] }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
