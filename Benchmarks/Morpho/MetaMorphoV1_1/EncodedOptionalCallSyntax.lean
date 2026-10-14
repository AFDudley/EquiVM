import Benchmarks.Morpho.MetaMorphoV1_1.SafeTransferAllocationSyntax

/-! Common source syntax for ABI-encoded SafeERC20 requests with explicit allocation. -/

open Stele ABI Ethereum

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

-- LIBRARY CANDIDATE: the encoded-call wrapper shared by safeTransfer and safeTransferFrom.
def encodedOptionalCallBody (encode : Expr) (size : UInt256) : List Stmt :=
  [.letDecl "data" none encode,
   .internalCall allocateFunction.name [.var cursorName, .intLit (Int.ofNat size.toNat)] cursorName,
   .internalCall allocatedOptionalReturnFunction.name
     [.var "token", .var "data", .var cursorName] "__c0",
   .return [.var "__c0"]]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
