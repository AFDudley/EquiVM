import Stele.Semantics
import Stele.SolidityLayout
import Stele.SolidityStorage
import Stele.MetaSolidityLayout

/-!
# CtorTruth — Stele specification for a constructor-equivalence smoke test

The payable empty constructor keeps the initcode trace small, while still exercising the
constructor-equivalence API and Solidity deployment hook.
-/

open Stele ABI

namespace CtorTruth

/-- The runtime transition is the same shape as `Truth.truth()`. -/
def truthTransition : TransitionDecl :=
  { name := "truth"
    params := []
    returnType := [(.elem .bool)]
    body :=
      [ .require (.binary .eq (.env .callvalue) (.intLit 0))
      , .return [(.boolLit true)] ] }

/-- A payable constructor avoids Solidity's non-payable constructor guard. -/
def ctor : ConstructorDecl :=
  { params := []
    body := [] }

/-- Stele specification of `CtorTruth`. -/
def contract : ContractDecl :=
  { name := "CtorTruth"
    storage := []
    ctor := ctor
    transitions := [truthTransition] }

end CtorTruth

/-- Configuration: empty storage backend and Solidity constructor deployment encoding. -/
def ctorTruthConfig : Config :=
  { storageBackend := solidityStorage! [([] : List StructDecl)] [CtorTruth.contract.storage]
    externalABI := defaultExternalCallABI
    selfDeployment := genSolidityConstructorDeployment CtorTruth.contract.ctor.params }
