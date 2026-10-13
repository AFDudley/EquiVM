import Examples.Caller.Spec
import Stele.Notation

/-!
# Caller spec in the Solidity-faithful Stele frontend

The `Caller` contract from `Examples/Caller/Spec.lean` written with `solidity%` and proven
definitionally equal to the AST spec.

* The spec's constructor body is empty (no non-payable guard), so the surface constructor is
  marked `payable` to suppress the auto-inserted guard.
* `t.pow2(n)` is the external call, bound to `tmp` as in the AST.
-/

open Stele Stele.Notation

namespace Caller.Syntax

def contractSyntax : ContractDecl := solidity% contract Caller {
  uint256 stored;

  constructor() payable { }

  function run(address t, uint256 n) external {
    var tmp = t.pow2(n);
    stored = tmp;
  }
}

theorem contractSyntax_eq : contractSyntax = Caller.callerContract := by rfl

end Caller.Syntax
