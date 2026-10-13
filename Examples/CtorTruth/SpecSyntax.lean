import Examples.CtorTruth.Spec
import Stele.Notation

/-!
# CtorTruth spec in the Solidity-faithful Stele frontend

The spec's constructor is payable with an empty body (no callvalue guard); `truth()` is
non-payable, so its guard is implicit.
-/

open Stele Stele.Notation

namespace CtorTruth.Syntax

def contractSyntax : ContractDecl := solidity% contract CtorTruth {
  constructor() payable { }

  function truth() external returns (bool) {
    return true;
  }
}

theorem contractSyntax_eq : contractSyntax = CtorTruth.contract := by rfl

end CtorTruth.Syntax
