import Benchmarks.Safe.ViaIR.ModulesSource
import Benchmarks.Safe.ViaIR.Calldata
import Benchmarks.Safe.ViaIR.Dispatch

/-! Boundary witness for the IR paginated-module array allocation. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000
set_option maxHeartbeats 800000

def safeIRModuleAllocationSize : UInt256 := UInt256.ofNat (2 ^ 59 - 1)

def safeIRModuleAllocationEnv : ExecutionEnv :=
  { (default : ExecutionEnv) with
    code := safeBytecode
    codeOwner := AccountAddress.ofNat 4096
    source := AccountAddress.ofNat 4096
    calldata := ⟨#[0xcc, 0x2f, 0x84, 0x52]⟩ ++ (⟨1⟩ : UInt256).toByteArray ++
      safeIRModuleAllocationSize.toByteArray
    weiValue := ⟨0⟩
    perm := true }

def safeIRModuleAllocationAccounts : AccountMap :=
  (default : AccountMap).insert (AccountAddress.ofNat 4096)
    { (default : Account) with
      storage := (default : Storage).insert (mapSlot ⟨1⟩ ⟨1⟩) ⟨1⟩ }

def safeIRModuleAllocationState : State :=
  initState safeIRModuleAllocationAccounts safeIRModuleAllocationAccounts
    (.ofUInt256 ⟨100000⟩) default safeIRModuleAllocationEnv

theorem safeIRModuleAllocationPremises :
    safeIRModuleAllocationEnv.code = safeBytecode ∧
      safeIRModuleAllocationEnv.calldata.size < UInt256.size ∧
      safeIRModuleAllocationAccounts.get? safeIRModuleAllocationEnv.codeOwner ≠ none ∧
      selectorDispatchMsg contract safeIRModuleAllocationEnv.calldata =
        some getmodulespaginatedTransition := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> native_decide

theorem safeIRModuleAllocationStorage :
    moduleLink safeIRModuleAllocationState ⟨1⟩ = ⟨1⟩ := by native_decide

theorem safeIRModuleAllocationDecoding :
    config.externalABI.decodeCalldata?
      (getmodulespaginatedTransition.params.map Param.name)
      (transitionSignature getmodulespaginatedTransition).paramTypes
      safeIRModuleAllocationEnv.calldata =
        some (modulesArgs ⟨1⟩ safeIRModuleAllocationSize) := by
  have hs : calldataWord safeIRModuleAllocationEnv.calldata 4 = ⟨1⟩ := by native_decide
  have hn : calldataWord safeIRModuleAllocationEnv.calldata 36 = safeIRModuleAllocationSize := by
    native_decide
  have hd := decodeCalldata_addr_uint256_ok (cd := safeIRModuleAllocationEnv.calldata)
    (x := "start") (y := "pageSize")
    (by native_decide) (by native_decide) (by rw [hs]; decide)
  simpa only [hs, hn] using hd

theorem safeIRModuleAllocationExecution :
    (match Ξ safeIRModuleAllocationAccounts safeIRModuleAllocationAccounts ⟨100000⟩
        default safeIRModuleAllocationEnv with
      | .ok (.revert gas out) => gas == ⟨99080⟩ &&
          out == (⟨#[0x4e, 0x48, 0x7b, 0x71]⟩ ++ (⟨0x41⟩ : UInt256).toByteArray)
      | _ => false) = true := by native_decide

theorem safeIRModuleAllocationSourceReturns :
    ∃ locals', ExecTransitionBody config contract safeIRModuleAllocationState
      (modulesArgs ⟨1⟩ safeIRModuleAllocationSize) getmodulespaginatedTransition.body
      (.returned { contract := contract, locals := locals' } safeIRModuleAllocationState
        (some [.array [], addressArrayValue ⟨1⟩])) := by
  have hp : LinkedPage (moduleLink safeIRModuleAllocationState)
      safeIRModuleAllocationSize.toNat (moduleLink safeIRModuleAllocationState ⟨1⟩) [] ⟨1⟩ := by
    rw [safeIRModuleAllocationStorage]
    exact .stop (.inr (.inr rfl))
  simpa only [List.map_nil, modulesPageNext, if_pos rfl] using
    safeModulesSourceSuccess safeIRModuleAllocationState ⟨1⟩ safeIRModuleAllocationSize
      (by decide) rfl (.inl rfl) (by decide) (by decide) hp (.inl rfl)

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

private theorem iteFalseResult {cfg f s cond body r}
    (h : ExecStmt cfg f s (.ite cond body []) r)
    (he : evalExpr? cfg f s cond = .ok (.bool false)) : r = .ok f s := by
  cases h with
  | iteTrue ht _ => rw [he] at ht; cases ht
  | iteFalse _ hb => cases hb; rfl
  | iteCondRevert hf => rw [he] at hf; cases hf

private theorem consTail {cfg f s stmt tail r f' s'}
    (h : ExecBlock cfg f s (stmt :: tail) r)
    (hs : ∀ result, ExecStmt cfg f s stmt result → result = .ok f' s') :
    ExecBlock cfg f' s' tail r := by
  cases h with
  | consNormal hstmt ht => have he := hs _ hstmt; cases he; exact ht
  | consReturn hstmt | consBreak hstmt | consContinue hstmt | consRevert hstmt
      | consStatic hstmt => have he := hs _ hstmt; cases he

private theorem moduleAllocationCannotRevert
    (h : ExecBlock config
      { contract := contract, locals := modulesArgs ⟨1⟩ safeIRModuleAllocationSize }
      safeIRModuleAllocationState getmodulespaginatedTransition.body .reverted) : False := by
  have h1 := consTail h (fun _ hs ↦ requireResult hs (by native_decide))
  have h2 := consTail h1 (fun _ hs ↦ requireResult hs (by native_decide))
  have h3 := consTail h2 (fun _ hs ↦ requireResult hs (by native_decide))
  have h4 := consTail h3 (fun _ hs ↦ requireResult hs (by native_decide))
  have h5 := consTail h4 (fun _ hs ↦ letResult (value := .int 0) hs (by native_decide))
  have h6 := consTail h5 (fun _ hs ↦ letResult (value := addressArrayValue ⟨1⟩) hs
    (by native_decide))
  have h7 := consTail h6 (fun _ hs ↦ letResult (value := addressArrayValue ⟨0⟩) hs
    (by native_decide))
  have h8 := consTail h7 (fun _ hs ↦ whileFalseResult hs (by native_decide))
  have h9 := consTail h8 (fun _ hs ↦ iteFalseResult hs (by native_decide))
  have h10 := consTail h9 (fun _ hs ↦ letResult (value := .array []) hs (by native_decide))
  have h11 := consTail h10 (fun _ hs ↦ letResult (value := .int 0) hs (by native_decide))
  have h12 := consTail h11 (fun _ hs ↦ letResult (value := addressArrayValue ⟨1⟩) hs
    (by native_decide))
  have h13 := consTail h12 (fun _ hs ↦ whileFalseResult hs (by native_decide))
  cases h13 with
  | consNormal hs _ => cases hs
  | consRevert hs =>
      cases hs with
      | returnRevert hf =>
          revert hf
          native_decide

theorem safeIRModuleAllocationSourceCannotRevert :
    ¬ExecTransitionBody config contract safeIRModuleAllocationState
      (modulesArgs ⟨1⟩ safeIRModuleAllocationSize) getmodulespaginatedTransition.body
      .reverted := by
  intro h
  cases h with
  | execBlockRevert hb => exact moduleAllocationCannotRevert hb

theorem safeIRModuleAllocationNotRefines :
    ¬runtimeRefinementFor config contract safeIRModuleAllocationAccounts
      safeIRModuleAllocationAccounts ⟨100000⟩ default safeIRModuleAllocationEnv := by
  intro h
  have hex := safeIRModuleAllocationExecution
  have hsel := safeIRModuleAllocationPremises.2.2.2
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
        rw [safeIRModuleAllocationDecoding] at hdec
        cases hdec
        cases hstate
        exact safeIRModuleAllocationSourceCannotRevert hbody
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
    rw [safeIRModuleAllocationDecoding] at hdec
    cases hdec
  | outOfGas hevm => rw [hevm] at hex; cases hex

theorem safeIRModuleAllocationCorrectedBound (pageSize : Nat) :
    32 * pageSize + 160 ≤ 2 ^ 64 - 1 ↔ pageSize ≤ 2 ^ 59 - 6 := by omega

theorem safeIRModuleAllocationRejectedByCorrectedBound :
    ¬safeIRModuleAllocationSize.toNat ≤ 2 ^ 59 - 6 := by decide

end Benchmarks.Safe.ViaIR
