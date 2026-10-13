import Benchmarks.Safe.ViaIR.GetOwnersSource
import Benchmarks.Safe.ViaIR.Calldata
import Benchmarks.Safe.ViaIR.IRLengthCheck

/-! Regression witness for the IR owner-array allocation-pointer check. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

def safeIROwnerAllocationCount : UInt256 := UInt256.ofNat (2 ^ 59 - 1)

def safeIROwnerAllocationEnv : ExecutionEnv :=
  { (default : ExecutionEnv) with
    code := safeBytecode
    codeOwner := AccountAddress.ofNat 4096
    source := AccountAddress.ofNat 4096
    calldata := ⟨#[0xa0, 0xe6, 0x7e, 0x2b]⟩
    weiValue := ⟨0⟩
    perm := true }

def safeIROwnerAllocationAccounts : AccountMap :=
  (default : AccountMap).insert (AccountAddress.ofNat 4096)
    { (default : Account) with
      storage := (default : Storage).insert ⟨3⟩ safeIROwnerAllocationCount |>.insert
        (mapSlot ⟨1⟩ ⟨2⟩) ⟨1⟩ }

def safeIROwnerAllocationState : State :=
  initState safeIROwnerAllocationAccounts safeIROwnerAllocationAccounts
    (.ofUInt256 ⟨100000⟩) default safeIROwnerAllocationEnv

theorem safeIROwnerAllocationPremises :
    safeIROwnerAllocationEnv.code = safeBytecode ∧
      safeIROwnerAllocationEnv.calldata.size < UInt256.size ∧
      safeIROwnerAllocationAccounts.get? safeIROwnerAllocationEnv.codeOwner ≠ none ∧
      selectorDispatchMsg contract safeIROwnerAllocationEnv.calldata =
        some getownersTransition := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> native_decide

theorem safeIROwnerAllocationStorage :
    ownerCount safeIROwnerAllocationState = safeIROwnerAllocationCount ∧
      ownerLink safeIROwnerAllocationState ⟨1⟩ = ⟨1⟩ := by native_decide

theorem safeIROwnerAllocationDecoding :
    config.externalABI.decodeCalldata?
      (getownersTransition.params.map Param.name)
      (transitionSignature getownersTransition).paramTypes safeIROwnerAllocationEnv.calldata =
        some ∅ := by
  exact safeDecodeCalldata_empty_ok (cd := safeIROwnerAllocationEnv.calldata)
    (by decide) (by decide)

theorem safeIROwnerAllocationExecution :
    (match Ξ safeIROwnerAllocationAccounts safeIROwnerAllocationAccounts ⟨100000⟩
        default safeIROwnerAllocationEnv with
      | .ok (.revert gas out) => gas == ⟨97240⟩ &&
          out == (⟨#[0x4e, 0x48, 0x7b, 0x71]⟩ ++ (⟨0x41⟩ : UInt256).toByteArray)
      | _ => false) = true := by native_decide

theorem safeIROwnerAllocationSourceReturns :
    ExecTransitionBody config contract safeIROwnerAllocationState ∅ getownersTransition.body
      (.returned
        { contract := contract, locals := getOwnersInitialLocals safeIROwnerAllocationState }
        safeIROwnerAllocationState
        (some [.array ((List.replicate (ownerCount safeIROwnerAllocationState).toNat ⟨0⟩).map
          addressArrayValue)])) := by
  have hl := safeGetOwnersInitialLocals safeIROwnerAllocationState
  have hc := safeGetOwnersCondition safeIROwnerAllocationState hl
    (solcAddrMask_result_canonical _)
  rw [safeIROwnerAllocationStorage.2] at hc
  apply ExecFuncBody.execBlockRet
  apply safeGetOwnersPrefix safeIROwnerAllocationState rfl
    (by rw [safeIROwnerAllocationStorage.1]; decide)
  exact .consNormal (.whileFalse (by simpa using hc))
    (safeGetOwnersReturn safeIROwnerAllocationState hl)

private theorem requireResult {cfg f s cond r}
    (h : ExecStmt cfg f s (.require cond) r)
    (he : evalExpr? cfg f s cond = .ok (.bool true)) : r = .ok f s := by
  cases h <;> simp_all

private theorem letResult {cfg f s name ty expr value r}
    (h : ExecStmt cfg f s (.letDecl name ty expr) r)
    (he : evalExpr? cfg f s expr = .ok value) :
    r = .ok { f with locals := f.locals.insert name value } s := by
  cases h <;> simp_all

private theorem whileFalseResult {cfg f s cond body r}
    (h : ExecStmt cfg f s (.while cond body) r)
    (he : evalExpr? cfg f s cond = .ok (.bool false)) : r = .ok f s := by
  cases h <;> simp_all

private theorem consTail {cfg f s stmt tail r f' s'}
    (h : ExecBlock cfg f s (stmt :: tail) r)
    (hs : ∀ result, ExecStmt cfg f s stmt result → result = .ok f' s') :
    ExecBlock cfg f' s' tail r := by
  cases h with
  | consNormal hstmt ht => have he := hs _ hstmt; cases he; exact ht
  | consReturn hstmt | consBreak hstmt | consContinue hstmt | consRevert hstmt
      | consStatic hstmt => have he := hs _ hstmt; cases he

private theorem ownerAllocationCannotRevert
    (h : ExecBlock config { contract := contract, locals := ∅ } safeIROwnerAllocationState
      getownersTransition.body .reverted) : False := by
  let evm := safeIROwnerAllocationState
  let frame : Frame := { contract := contract, locals := ∅ }
  let words := List.replicate (ownerCount evm).toNat (⟨0⟩ : UInt256)
  have hvalue := evalCallvalueEq_true (cfg := config) (solm := frame)
    (evm := evm) (by rfl)
  have hguard : evalExpr? config frame evm (leE (.storage ownerCountRef) maxMemoryLength) =
      .ok (.bool true) := by
    have he := safeGetOwnersCountGuard evm
    rw [safeIROwnerAllocationStorage.1] at he
    exact he
  have hnew : evalExpr? config frame evm (.newArray addrSt (.storage ownerCountRef)) =
      .ok (.array (words.map addressArrayValue)) := by
    rw [evalExpr?, safeEvalOwnerCount evm ∅ (by simp)]
    simp [EvalResult.bind, bind, pure, defaultValue?, addrSt, addressArrayValue, words]
  have htail := consTail (consTail h (fun _ hs ↦ requireResult hs hvalue))
    (fun _ hs ↦ requireResult hs hguard)
  have ha := consTail htail (fun _ hs ↦ letResult hs hnew)
  have hi := consTail ha (fun _ hs ↦ letResult (value := .int 0) hs
    (by simp [evalExpr?, pure]))
  let locals := ((∅ : Store).insert "array" (.array (words.map addressArrayValue))).insert
    "index" (.int 0)
  have hc := safeEvalOwnerLink evm locals sentinelAddr ⟨1⟩
    (by simp [locals]) (by decide) (safeEvalOwnerSentinel evm _)
  have hl := consTail hi (fun _ hs ↦ letResult hs hc)
  change ExecBlock config { contract := contract, locals := getOwnersInitialLocals evm }
    evm [getOwnersLoop, .return [.var "array"]] .reverted at hl
  have hcond := safeGetOwnersCondition evm (safeGetOwnersInitialLocals evm)
    (solcAddrMask_result_canonical _)
  rw [safeIROwnerAllocationStorage.2] at hcond
  have hr := consTail hl (fun _ hs ↦ whileFalseResult hs (by simpa using hcond))
  have he := evalExprs?_singleton (evalLocalValue (cfg := config) (evm := evm)
    (frame := { contract := contract, locals := getOwnersInitialLocals evm })
    (safeGetOwnersInitialLocals evm).array)
  cases hr with
  | consNormal hs _ => cases hs
  | consRevert hs => cases hs with | returnRevert hf => rw [he] at hf; cases hf

theorem safeIROwnerAllocationSourceCannotRevert :
    ¬ExecTransitionBody config contract safeIROwnerAllocationState ∅
      getownersTransition.body .reverted := by
  intro h
  cases h with
  | execBlockRevert hb => exact ownerAllocationCannotRevert hb

theorem safeIROwnerAllocationNotRefines :
    ¬runtimeRefinementFor config contract safeIROwnerAllocationAccounts
      safeIROwnerAllocationAccounts ⟨100000⟩ default safeIROwnerAllocationEnv := by
  intro h
  have hex := safeIROwnerAllocationExecution
  have hsel := safeIROwnerAllocationPremises.2.2.2
  cases h with
  | execution hxi hsolm hrel =>
    cases hrel with
    | revert hevm hsource =>
      cases hsource
      cases hsolm with
      | intro hdispatch hsig hdec hstate hbody =>
        rw [hsel] at hdispatch
        cases hdispatch
        subst hsig
        rw [safeIROwnerAllocationDecoding] at hdec
        cases hdec
        cases hstate
        exact safeIROwnerAllocationSourceCannotRevert hbody
      | fallback hdispatch _ _ _ _ _ _ => rw [hsel] at hdispatch; cases hdispatch
      | receive hrecv _ _ _ _ =>
        change none = some _ at hrecv
        cases hrecv
    | success hevm _ _ _ | invalidHalt hevm _ | staticHalt hevm _ =>
      rw [hxi, hevm] at hex
      cases hex
  | noDispatch hd _ => simp only [dispatchMsg, hsel] at hd; cases hd
  | decodingFailed hd hsig hdec _ =>
    rw [hsel] at hd
    cases hd
    subst hsig
    rw [safeIROwnerAllocationDecoding] at hdec
    cases hdec
  | outOfGas hevm => rw [hevm] at hex; cases hex

theorem safeIROwnerAllocationCorrectedBound (count : Nat) :
    32 * count + 160 ≤ 2 ^ 64 - 1 ↔ count ≤ 2 ^ 59 - 6 := by omega

theorem safeIROwnerAllocationRejectedByCorrectedBound :
    ¬safeIROwnerAllocationCount.toNat ≤ 2 ^ 59 - 6 := by decide

end Benchmarks.Safe.ViaIR
