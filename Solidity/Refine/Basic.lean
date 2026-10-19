import Solidity.Semantics
import Stele.Refine

/-!
# Refinement of EVM bytecode by a Solidity spec

Same layering as `Stele/Refine.lean` (result equivalence → fixed-input relations → ∀-closures →
contract level), with two additions the Solidity semantics makes possible:
* revert data is compared exactly (`Error(string)`, `Panic(uint256)`, custom errors, empty);
* the final log series and created-account set must coincide (both sides start from the same
  substate `A`).
`INVALID` is not a spec revert: solc 0.8 reverts with `Panic` data, so a stray `INVALID` is a
genuine crash.  Calldata the spec cannot decode must revert: with empty data, or with
`Panic(0x41)` when the argument decoder allocates memory for a dynamic argument.

Nondeterminism (`gasleft()`, gas and non-log substate handed to sub-calls) is quantified once,
existentially over an `Oracle`: the bytecode's behaviour must be one the spec can exhibit.

Immutables: a deployment runs the constructor, which returns the runtime code for the immutables
it set (`runtimeCodeOf`), and every later call runs that code; the spec's runtime relation is
stated for the immutables the constructor deployed (`contractRefinementWF`).  A top-level call
is never executed in static mode (`I.perm = true`); the static-mode halt of Sol⁻'s relation is not
modelled here.
-/

namespace Solidity

open ABI

abbrev EVMResult := Except Ethereum.EVM.ExecutionException
  (Ethereum.ExecutionResult (Ethereum.AccountMap × Ethereum.UInt256 × Ethereum.Substate))

/-- Equivalence of returned data; return slots always exist, so there is no fall-through case. -/
inductive returnDataEquiv (o : ByteArray) (vs : List Stele.Value) : Stele.ReturnConvention → Prop where
  | abi {tys} : encodeReturnValues? tys vs = some o → returnDataEquiv o vs (.abi tys)
  | rawBytes : vs = [.bytes o] → returnDataEquiv o vs .rawBytes

/-- Accounts, return data, revert data, logs and created accounts. -/
inductive execResultsEquiv (evmRes : EVMResult) (res : TopResult) (conv : Stele.ReturnConvention) : Prop where
  | success :
    evmRes = .ok (.success (σ', g', A') out) →
    res = .returned m vs →
    σ' = m.evm.accountMap →
    A'.logSeries = m.evm.substate.logSeries →
    A'.createdAccounts = m.evm.substate.createdAccounts →
    returnDataEquiv out vs conv →
    execResultsEquiv evmRes res conv
  | revert :
    evmRes = .ok (.revert g out) →
    res = .reverted out →
    execResultsEquiv evmRes res conv
  /-- Inline assembly ended the call (`return` / `stop`): the raw return data, whatever the
      convention. -/
  | halt :
    evmRes = .ok (.success (σ', g', A') out) →
    res = .halted m out →
    σ' = m.evm.accountMap →
    A'.logSeries = m.evm.substate.logSeries →
    A'.createdAccounts = m.evm.substate.createdAccounts →
    execResultsEquiv evmRes res conv

/-- Revert data of a call whose arguments cannot be decoded: empty, or `Panic(0x41)` when the
    decoder allocates memory for a dynamic argument (`hasDynamicMemoryParam`). -/
def decodeFailureData (env : TypeEnv) (d : FnDecl) (out : ByteArray) : Prop :=
  out = ByteArray.empty ∨ (hasDynamicMemoryParam env d = true ∧ out = panicData 0x41)

/-- Runtime refinement of one message call at fixed inputs, the spec running with `immutables`
    (`∅` for a contract without). -/
inductive runtimeRefinementFor (cfg : Config) (fc : FlatContract)
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) (immutables : Store := ∅) : Prop where
  | execution {Ξ_res res conv} :
    Ethereum.EVM.Ξ σ σ₀ g A I = Ξ_res →
    (∃ o : Oracle, solidityExec cfg o fc immutables σ σ₀ g A I res conv ∧ execResultsEquiv Ξ_res res conv) →
    runtimeRefinementFor cfg fc σ σ₀ g A I immutables
  | noDispatch :
    dispatches fc I.calldata = false →
    Ethereum.EVM.Ξ σ σ₀ g A I = .ok (.revert g' ByteArray.empty) →
    runtimeRefinementFor cfg fc σ σ₀ g A I immutables
  | decodingFailed {e fn g' out} :
    selectorDispatch fc I.calldata = some e → fc.fns[e.fn]? = some fn →
    payableOrNoValue fn.decl I →
    decodeCallArgs cfg fc.types fn.decl I.calldata = none →
    Ethereum.EVM.Ξ σ σ₀ g A I = .ok (.revert g' out) →
    decodeFailureData fc.types fn.decl out →
    runtimeRefinementFor cfg fc σ σ₀ g A I immutables
  | outOfGas :
    Ethereum.EVM.Ξ σ σ₀ g A I = .error .OutOfGass →
    runtimeRefinementFor cfg fc σ σ₀ g A I immutables

abbrev StorageWF := Stele.StorageWF
abbrev GasBound := Stele.GasBound

/-- Runtime refinement over all admissible inputs, under a storage precondition and a bound on
    the starting gas. -/
inductive runtimeRefinementWithWF (wf : StorageWF) (gasBound : GasBound) (cfg : Config)
    (bytecode : ByteArray) (fc : FlatContract) (immutables : Store := ∅) : Prop where
  | intro :
    (∀ (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
      (I : Ethereum.ExecutionEnv),
    I.code = bytecode →
    I.calldata.size < Ethereum.UInt256.size →
    I.perm = true →
    wf σ I →
    gasBound g →
    runtimeRefinementFor cfg fc σ σ₀ g A I immutables) →
    runtimeRefinementWithWF wf gasBound cfg bytecode fc immutables

inductive runtimeRefinement (cfg : Config) (bytecode : ByteArray) (fc : FlatContract)
    (immutables : Store := ∅) : Prop where
  | intro :
    (∀ (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
      (I : Ethereum.ExecutionEnv),
    I.code = bytecode →
    I.calldata.size < Ethereum.UInt256.size →
    I.perm = true →
    runtimeRefinementFor cfg fc σ σ₀ g A I immutables) →
    runtimeRefinement cfg bytecode fc immutables

theorem runtimeRefinementWithWF_trivial_iff {cfg : Config} {bytecode : ByteArray} {fc : FlatContract}
    {immutables : Store} :
    runtimeRefinementWithWF Stele.trivialStorageWF Stele.noGasBound cfg bytecode fc immutables ↔
      runtimeRefinement cfg bytecode fc immutables := by
  constructor
  · rintro ⟨h⟩
    exact ⟨fun σ σ₀ g A I hcode hsize hperm => h σ σ₀ g A I hcode hsize hperm trivial trivial⟩
  · rintro ⟨h⟩
    exact ⟨fun σ σ₀ g A I hcode hsize hperm _ _ => h σ σ₀ g A I hcode hsize hperm⟩

/-! ## Constructors -/

/-- The EVM's deployment returns the runtime code of the immutables the constructor set. -/
inductive ctorResultEquiv (evmRes : EVMResult) (res : CtorResult) (runtimeCodeOf : Store → ByteArray) : Prop where
  | success :
    evmRes = .ok (.success (σ', g', A') out) →
    res = .ok m imms →
    σ' = m.evm.accountMap →
    A'.logSeries = m.evm.substate.logSeries →
    A'.createdAccounts = m.evm.substate.createdAccounts →
    out = runtimeCodeOf imms →
    ctorResultEquiv evmRes res runtimeCodeOf
  | revert :
    evmRes = .ok (.revert g out) →
    res = .reverted out →
    ctorResultEquiv evmRes res runtimeCodeOf

/-- The immutables a constructor run deploys: those of its result on success, none otherwise. -/
def deployedImmutables : CtorResult → Option Store
  | .ok _ imms => some imms
  | .reverted _ => none

/-- Constructor refinement at fixed deployment inputs, exposing the immutables the spec's run
    deployed (`none` if it did not succeed). -/
inductive constructorRefinementFor (cfg : Config) (fc : FlatContract) (args : List Stele.Value)
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) (runtimeCodeOf : Store → ByteArray) : Option Store → Prop where
  | execution {Ξ_res res} :
    Ethereum.EVM.Ξ σ σ₀ g A I = Ξ_res →
    (∃ o : Oracle, solidityCtorExec cfg o fc args σ σ₀ g A I res ∧ ctorResultEquiv Ξ_res res runtimeCodeOf) →
    constructorRefinementFor cfg fc args σ σ₀ g A I runtimeCodeOf (deployedImmutables res)
  | outOfGas :
    Ethereum.EVM.Ξ σ σ₀ g A I = .error .OutOfGass →
    constructorRefinementFor cfg fc args σ σ₀ g A I runtimeCodeOf none

/-- The immutables a deployed contract runs with: the declared ones of the constructor's final
    store. -/
def restrictImmutables (fc : FlatContract) (imms : Store) : Store :=
  fc.immutableVars.foldl (fun acc v =>
    match imms.get? (immName v.name) with
    | some l => acc.insert (immName v.name) l
    | none => acc) ∅

theorem restrictImmutables_noImmutables {fc : FlatContract} {imms : Store}
    (h : fc.immutableVars = []) : restrictImmutables fc imms = ∅ := by
  simp [restrictImmutables, h]

/-- Whether `imms` gives every declared immutable a canonical value of its declared type (it
    round-trips through the ABI/storage domain). -/
def immutablesFit (fc : FlatContract) (imms : Store) : Prop :=
  ∀ v ∈ fc.immutableVars, ∃ l, imms.get? (immName v.name) = some l ∧
    ∃ sv, scalarToAbi l.val = some sv ∧ scalarOfAbi fc.types v.ty sv = some l.val

/-- Deployment refinement at fixed inputs: the constructor is equivalent, and whatever it deployed
    is equivalent at runtime with its immutables. -/
def deploymentRefinement (wf : StorageWF) (gasBound : GasBound) (cfg : Config) (fc : FlatContract)
    (args : List Stele.Value) (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) (runtimeCodeOf : Store → ByteArray) : Prop :=
  ∃ imms?, constructorRefinementFor cfg fc args σ σ₀ g A I runtimeCodeOf imms? ∧
    ∀ imms, imms? = some imms →
      runtimeRefinementWithWF wf gasBound cfg (runtimeCodeOf imms) fc (restrictImmutables fc imms)

/-- Top-level contract refinement under a storage precondition and a gas bound for runtime calls:
    deployment refinement at every deployment of `initcode` (the arguments admitted by
    `cfg.selfDeployment`), for one `runtimeCodeOf` shared by all of them. -/
inductive contractRefinementWF (wf : StorageWF) (gasBound : GasBound) (cfg : Config)
    (initcode : ByteArray) (fc : FlatContract) : Prop where
  | intro (runtimeCodeOf : Store → ByteArray) :
    (∀ (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
      (I : Ethereum.ExecutionEnv) (args : List Stele.Value) (deployedInitcode : ByteArray),
      cfg.selfDeployment initcode args = .some deployedInitcode →
      I.code = deployedInitcode →
      I.calldata = .empty →
      I.perm = true →
      deploymentRefinement wf gasBound cfg fc args σ σ₀ g A I runtimeCodeOf) →
    contractRefinementWF wf gasBound cfg initcode fc

/-- Top-level contract refinement: deployment + every message call. -/
abbrev contractRefinement (cfg : Config) (initcode : ByteArray) (fc : FlatContract) : Prop :=
  contractRefinementWF Stele.trivialStorageWF Stele.noGasBound cfg initcode fc

/-! ### Proving it: constructor and runtime separately -/

/-- The immutables of a successful constructor run are well-typed (other results carry none). -/
def ctorImmutablesFit (fc : FlatContract) : CtorResult → Prop
  | .ok _ imms => immutablesFit fc imms
  | .reverted _ => True

theorem ctorImmutablesFit_noImmutables {fc : FlatContract} {res : CtorResult}
    (h : fc.immutableVars = []) : ctorImmutablesFit fc res := by
  cases res with
  | ok m imms => intro v hv; simp [h] at hv
  | reverted d => trivial

/-- The constructor half as proved: the deployment is equivalent and the deployed immutables are
    well-typed (automatic for a contract without immutables). -/
inductive typedConstructorRefinementFor (cfg : Config) (fc : FlatContract) (args : List Stele.Value)
    (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
    (I : Ethereum.ExecutionEnv) (runtimeCodeOf : Store → ByteArray) : Prop where
  | execution {Ξ_res res} :
    Ethereum.EVM.Ξ σ σ₀ g A I = Ξ_res →
    (∃ o : Oracle, solidityCtorExec cfg o fc args σ σ₀ g A I res ∧ ctorResultEquiv Ξ_res res runtimeCodeOf) →
    (hfit : ctorImmutablesFit fc res := by exact ctorImmutablesFit_noImmutables (by rfl)) →
    typedConstructorRefinementFor cfg fc args σ σ₀ g A I runtimeCodeOf
  | outOfGas :
    Ethereum.EVM.Ξ σ σ₀ g A I = .error .OutOfGass →
    typedConstructorRefinementFor cfg fc args σ σ₀ g A I runtimeCodeOf

/-- `typedConstructorRefinementFor` at every deployment of `initcode`. -/
inductive typedConstructorRefinement (cfg : Config) (initcode : ByteArray) (fc : FlatContract)
    (runtimeCodeOf : Store → ByteArray) : Prop where
  | intro :
    (∀ (σ σ₀ : Ethereum.AccountMap) (g : Ethereum.UInt256) (A : Ethereum.Substate)
      (I : Ethereum.ExecutionEnv) (args : List Stele.Value) (deployedInitcode : ByteArray),
    cfg.selfDeployment initcode args = .some deployedInitcode →
    I.code = deployedInitcode →
    I.calldata = .empty →
    I.perm = true →
    typedConstructorRefinementFor cfg fc args σ σ₀ g A I runtimeCodeOf) →
    typedConstructorRefinement cfg initcode fc runtimeCodeOf

theorem typedConstructorRefinementFor.toDeployment {wf : StorageWF} {gasBound : GasBound} {cfg : Config}
    {fc : FlatContract} {args : List Stele.Value} {σ σ₀ : Ethereum.AccountMap} {g : Ethereum.UInt256}
    {A : Ethereum.Substate} {I : Ethereum.ExecutionEnv} {runtimeCodeOf : Store → ByteArray}
    (h : typedConstructorRefinementFor cfg fc args σ σ₀ g A I runtimeCodeOf)
    (hrt : ∀ imms, immutablesFit fc imms →
      runtimeRefinementWithWF wf gasBound cfg (runtimeCodeOf imms) fc (restrictImmutables fc imms)) :
    deploymentRefinement wf gasBound cfg fc args σ σ₀ g A I runtimeCodeOf := by
  cases h with
  | outOfGas hoog => exact ⟨none, .outOfGas hoog, fun _ h => by cases h⟩
  | @execution _ res hΞ hex hfit =>
    refine ⟨_, .execution hΞ hex, fun imms himms => ?_⟩
    cases res with
    | ok m imms' => cases himms; exact hrt _ hfit
    | reverted _ => cases himms

/-- **The usual proof route**: a constructor proof for some `runtimeCodeOf`, and a runtime proof
    of `runtimeCodeOf imms` for every well-typed immutables store `imms`. -/
theorem contractRefinementWF.of_runtime {wf : StorageWF} {gasBound : GasBound} {cfg : Config}
    {initcode : ByteArray} {fc : FlatContract} {runtimeCodeOf : Store → ByteArray}
    (hctor : typedConstructorRefinement cfg initcode fc runtimeCodeOf)
    (hrt : ∀ imms, immutablesFit fc imms →
      runtimeRefinementWithWF wf gasBound cfg (runtimeCodeOf imms) fc (restrictImmutables fc imms)) :
    contractRefinementWF wf gasBound cfg initcode fc :=
  .intro runtimeCodeOf fun σ σ₀ g A I args d hdeploy hcode hcalldata hperm =>
    match hctor with
    | ⟨h⟩ => (h σ σ₀ g A I args d hdeploy hcode hcalldata hperm).toDeployment hrt

/-- Constant runtime code (no immutables). -/
def constCode (runtimeCode : ByteArray) : Store → ByteArray := fun _ => runtimeCode

/-- **Contracts without immutables**: the constructor returns `runtimeCode`, which is equivalent to
    the spec under the storage precondition `wf` and gas bound `gasBound`. -/
theorem contractRefinementWF.of_constant {wf : StorageWF} {gasBound : GasBound} {cfg : Config}
    {initcode runtimeCode : ByteArray} {fc : FlatContract}
    (hctor : typedConstructorRefinement cfg initcode fc (constCode runtimeCode))
    (hrt : runtimeRefinementWithWF wf gasBound cfg runtimeCode fc)
    (himm : fc.immutableVars = [] := by rfl) :
    contractRefinementWF wf gasBound cfg initcode fc :=
  contractRefinementWF.of_runtime hctor fun imms _ => by
    rw [restrictImmutables_noImmutables himm]
    exact hrt

/-- **Contracts without immutables**: the constructor returns `runtimeCode`, which is equivalent to
    the spec. -/
theorem contractRefinement.of_constant {cfg : Config} {initcode runtimeCode : ByteArray} {fc : FlatContract}
    (hctor : typedConstructorRefinement cfg initcode fc (constCode runtimeCode))
    (hrt : runtimeRefinement cfg runtimeCode fc)
    (himm : fc.immutableVars = [] := by rfl) :
    contractRefinement cfg initcode fc :=
  contractRefinementWF.of_constant hctor (runtimeRefinementWithWF_trivial_iff.mpr hrt) himm

end Solidity
