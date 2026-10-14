import Benchmarks.Morpho.MetaMorphoV1_1.SpecSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDecimalsSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.ForceApproveAllocationSyntax

/-! Memory reservations and cursor propagation in the constructor.

The creation code starts at cursor 480, copies the complete encoded arguments, copies
both strings to separate buffers, then allocates three empty strings and the version
string "1". The first external query also returns its updated cursor, followed by the
192-byte domain-separator preimage. A successful strict decimals query reserves its
32-byte return, then force-approval propagates the cursor through its request and
return buffers. Each reservation uses the existing checked allocator.
-/

open Stele ABI

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

def constructorPaddedLengthExpr (param : Ident) : Expr :=
  .binary .mul (.intLit 32)
    (.binary .div
      (.binary .add (.arrayLength .localVar ⟨param, []⟩) (.intLit 31)) (.intLit 32))

def constructorEncodedLengthExpr : Expr :=
  .binary .add
    (.binary .add (.intLit 256) (constructorPaddedLengthExpr "__name"))
    (constructorPaddedLengthExpr "__symbol")

def constructorInputAllocation : List Stmt :=
  [.internalCall allocateFunction.name [.intLit 480, constructorEncodedLengthExpr] cursorName,
   .internalCall allocateFunction.name
     [.var cursorName, .binary .add (.intLit 32) (constructorPaddedLengthExpr "__name")]
     cursorName,
   .internalCall allocateFunction.name
     [.var cursorName, .binary .add (.intLit 32) (constructorPaddedLengthExpr "__symbol")]
     cursorName,
   .internalCall allocateFunction.name [.var cursorName, .intLit 32] cursorName,
   .internalCall allocateFunction.name [.var cursorName, .intLit 32] cursorName,
   .internalCall allocateFunction.name [.var cursorName, .intLit 32] cursorName,
   .internalCall allocateFunction.name [.var cursorName, .intLit 64] cursorName]

def allocatedConstructor : ConstructorDecl :=
  let source := Syntax.contractSyntax.ctor
  { source with
    body := source.body.take 1 ++ constructorInputAllocation ++
      (source.body.drop 1).take 2 ++ constructorDecimalsCall ++
      (source.body.drop 4).take 7 ++ [reserveBytes 192] ++
      (source.body.drop 11).take 14 ++ [reserveBytes 32] ++
      (source.body.drop 25).take 1 ++
      allocationBody (fun name =>
        if name == "SafeERC20_forceApprove" then some allocatedForceApproveFunction.name
        else none) (fun _ => 0) (source.body.drop 26) }

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
