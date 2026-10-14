import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawAllocationSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateCalldataSyntax

/-! Compiler allocation checks for the reallocation loop and its external calls. -/

open Stele ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def reallocateCursorCall (name : Ident) : Option Ident :=
  if name == "_accruedSupplyBalance" then some allocatedAccruedSupplyBalanceFunction.name
  else none

def reallocateReturnReserve (name : Ident) : Nat :=
  if name == "withdraw" || name == "supply" then 64 else 0

def reallocateRowGuard : Stmt :=
  .require (.binary .ne (.var "allocationTuple")
    (.structLit ABI.Solc08Calldata.decodeFailureTag []))

def reallocateCursorStatement : Stmt → Stmt
  | .for init cond post body =>
      .for init cond post ([reserveBytes 64, reserveBytes 160] ++
        body.take 1 ++ [reallocateRowGuard] ++
        allocationBody reallocateCursorCall reallocateReturnReserve (body.drop 1))
  | stmt => stmt

def allocatedReallocateTransition : TransitionDecl :=
  let source := Syntax.contractSyntax.transitions[34]!
  { source with
    body := source.body.take 4 ++ [.letDecl cursorName (some cursorType) (.intLit 128)] ++
      (source.body.drop 4).map reallocateCursorStatement }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
