import Benchmarks.Safe.ViaIR.StorageAtSource
import Benchmarks.Safe.ViaIR.WordPairDecoder

/-! Regression witness for the IR storage reader's final allocation-pointer guard. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000
set_option maxHeartbeats 800000

def safeIRStorageAllocationLength : UInt256 := UInt256.ofNat (2 ^ 59 - 1)

def safeIRStorageAllocationCalldata : ByteArray :=
  ⟨#[0x56, 0x24, 0xb2, 0x5b]⟩ ++
    (⟨0⟩ : UInt256).toByteArray ++ safeIRStorageAllocationLength.toByteArray

def safeIRStorageAllocationEnv : ExecutionEnv :=
  { (default : ExecutionEnv) with
    code := safeBytecode
    codeOwner := AccountAddress.ofNat 4096
    source := AccountAddress.ofNat 4096
    calldata := safeIRStorageAllocationCalldata
    weiValue := ⟨0⟩
    perm := true }

def safeIRStorageAllocationAccounts : AccountMap :=
  (default : AccountMap).insert (AccountAddress.ofNat 4096) default

def safeIRStorageAllocationState : State :=
  initState safeIRStorageAllocationAccounts safeIRStorageAllocationAccounts
    (.ofUInt256 ⟨100000⟩) default safeIRStorageAllocationEnv

theorem safeIRStorageAllocationPremises :
    safeIRStorageAllocationEnv.code = safeBytecode ∧
      safeIRStorageAllocationEnv.calldata.size < UInt256.size ∧
      safeIRStorageAllocationAccounts.get? safeIRStorageAllocationEnv.codeOwner ≠ none ∧
      selectorDispatchMsg contract safeIRStorageAllocationEnv.calldata =
        some getstorageatTransition := by
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> native_decide

theorem safeIRStorageAllocationDecoding :
    config.externalABI.decodeCalldata?
      (getstorageatTransition.params.map Param.name)
      (transitionSignature getstorageatTransition).paramTypes
      safeIRStorageAllocationEnv.calldata =
        some (storageAtArgs ⟨0⟩ safeIRStorageAllocationLength) := by
  have h0 : calldataWord safeIRStorageAllocationCalldata 4 = ⟨0⟩ := by native_decide
  have hn : calldataWord safeIRStorageAllocationCalldata 36 = safeIRStorageAllocationLength := by
    native_decide
  have hd := decodeWordPair (cd := safeIRStorageAllocationCalldata)
    (x := "offset") (y := "length") (by native_decide) (by native_decide)
  simpa only [h0, hn] using hd

theorem safeIRStorageAllocationSourceGuard :
    (UInt256.shiftLeft safeIRStorageAllocationLength (UInt256.ofNat 5)).toNat = 2 ^ 64 - 32 ∧
      (UInt256.shiftLeft safeIRStorageAllocationLength (UInt256.ofNat 5)).toNat ≤ 2 ^ 64 - 1 := by
  decide

theorem safeIRStorageAllocationExecution :
    (match Ξ safeIRStorageAllocationAccounts safeIRStorageAllocationAccounts ⟨100000⟩
        default safeIRStorageAllocationEnv with
      | .ok (.revert gas out) => gas == ⟨99481⟩ &&
          out == (⟨#[0x4e, 0x48, 0x7b, 0x71]⟩ ++ (⟨0x41⟩ : UInt256).toByteArray)
      | _ => false) = true := by
  native_decide

private theorem pureConsTail {cfg f s stmt tail r f' s'}
    (hs : ∀ result, ExecStmt cfg f s stmt result → result = .ok f' s')
    (h : ExecBlock cfg f s (stmt :: tail) r) : ExecBlock cfg f' s' tail r := by
  cases h with
  | consNormal hstmt ht =>
    have he := hs _ hstmt
    cases he
    exact ht
  | consReturn hstmt | consBreak hstmt | consContinue hstmt
  | consRevert hstmt | consStatic hstmt =>
    have he := hs _ hstmt
    cases he

private theorem localAssignResult {cfg f s ref expr f' s' r}
    (h : ExecStmt cfg f s (.assign .localVar ref expr) (.ok f' s'))
    (h' : ExecStmt cfg f s (.assign .localVar ref expr) r) : r = .ok f' s' := by
  cases h with
  | assign heval hstore => cases h' <;> simp_all

private theorem twoLocalAssignments {cfg f s ref₁ e₁ ref₂ e₂ f' s' r}
    (h : ExecBlock cfg f s [.assign .localVar ref₁ e₁, .assign .localVar ref₂ e₂]
      (.ok f' s'))
    (h' : ExecBlock cfg f s [.assign .localVar ref₁ e₁, .assign .localVar ref₂ e₂] r) :
    r = .ok f' s' := by
  cases h with
  | consNormal h₁ ht =>
    cases ht with
    | consNormal h₂ ht =>
      cases ht
      have htail := pureConsTail (fun _ hs ↦ localAssignResult h₁ hs) h'
      have hnil := pureConsTail (fun _ hs ↦ localAssignResult h₂ hs) htail
      cases hnil
      rfl

private theorem storageLoopResult (evm : EVM.State) {locals offset len words fuel r}
    (hl : StorageAtLocals locals offset len words) (hn : words.length + fuel = len.toNat)
    (h : ExecStmt config { contract := contract, locals := locals } evm storageAtLoop r) :
    ∃ ls ws, r = .ok { contract := contract, locals := ls } evm ∧
      StorageAtLocals ls offset len ws := by
  induction fuel generalizing locals words r with
  | zero =>
    have hcond := safeStorageAtCondition evm hl
    have hc : (decide (words.length < len.toNat)) = false := by simp; omega
    rw [hc] at hcond
    cases h with
    | whileFalse => exact ⟨locals, words, rfl, hl⟩
    | whileCondRevert hc | whileTrue hc _ _ | whileReturn hc _
    | whileRevert hc _ | whileBreak hc _ | whileContinue hc _ _ | whileStatic hc _ =>
      rw [hcond] at hc
      cases hc
  | succ fuel ih =>
    have hcond := safeStorageAtCondition evm hl
    have hc : (decide (words.length < len.toNat)) = true := by simp; omega
    rw [hc] at hcond
    have hbound : len.toNat < UInt256.size := len.val.isLt
    have hstep := safeStorageAtStep evm hl (by omega)
    have hresult result (hs : ExecBlock config { contract := contract, locals := locals }
        evm storageAtLoopBody result) :
        result = .ok { contract := contract, locals :=
          storageAtNextLocals locals words (storageAtWord evm offset words.length) } evm :=
      twoLocalAssignments hstep hs
    cases h with
    | whileFalse hc | whileCondRevert hc => rw [hcond] at hc; cases hc
    | whileTrue _ hb ht =>
      have he := hresult _ hb
      cases he
      exact ih (safeStorageAtNextLocals hl)
        (by simp only [List.length_append, List.length_singleton]; omega) ht
    | whileReturn _ hb | whileRevert _ hb | whileBreak _ hb
    | whileContinue _ hb _ | whileStatic _ hb =>
      have he := hresult _ hb
      cases he

private theorem trueRequireResult {cfg f s cond r}
    (he : evalExpr? cfg f s cond = .ok (.bool true))
    (h : ExecStmt cfg f s (.require cond) r) : r = .ok f s := by
  cases h <;> simp_all

private theorem letResult {cfg f s name ty expr value r}
    (he : evalExpr? cfg f s expr = .ok value)
    (h : ExecStmt cfg f s (.letDecl name ty expr) r) :
    r = .ok { f with locals := f.locals.insert name value } s := by
  cases h <;> simp_all

private theorem storageReturnCannotRevert {evm locals offset len words}
    (hl : StorageAtLocals locals offset len words)
    (h : ExecBlock config { contract := contract, locals := locals } evm
      [.return [.var "result"]] .reverted) : False := by
  have he := evalExprs?_singleton (evalLocalValue (cfg := config) (evm := evm)
    (frame := { contract := contract, locals := locals }) hl.result)
  cases h with
  | consNormal hs _ => cases hs
  | consRevert hs => cases hs with
    | returnRevert hbad => rw [he] at hbad; cases hbad

theorem safeIRStorageAllocationSourceCannotRevert :
    ¬ExecTransitionBody config contract safeIRStorageAllocationState
      (storageAtArgs ⟨0⟩ safeIRStorageAllocationLength) getstorageatTransition.body .reverted := by
  intro h
  cases h with
  | execBlockRevert hb =>
    have hpay := evalCallvalueEq_true (cfg := config)
      (solm := { contract := contract, locals := storageAtArgs ⟨0⟩ safeIRStorageAllocationLength })
      (evm := safeIRStorageAllocationState) (by rfl)
    have hlen := safeStorageAtLengthGuard safeIRStorageAllocationState ⟨0⟩
      safeIRStorageAllocationLength
    simp only [safeIRStorageAllocationSourceGuard.2, decide_true] at hlen
    have hb₁ := pureConsTail (fun _ hs ↦ trueRequireResult hpay hs) hb
    have hb₂ := pureConsTail (fun _ hs ↦ trueRequireResult hlen hs) hb₁
    have he₁ : evalExpr? config
        { contract := contract, locals := storageAtArgs ⟨0⟩ safeIRStorageAllocationLength }
        safeIRStorageAllocationState emptyBytes = .ok (.bytes ByteArray.empty) := by
      simp [emptyBytes, evalExpr?, pure]
    have hb₃ := pureConsTail (fun _ hs ↦ letResult he₁ hs) hb₂
    have he₂ : evalExpr? config
        { contract := contract, locals :=
          (storageAtArgs ⟨0⟩ safeIRStorageAllocationLength).insert "result"
            (.bytes ByteArray.empty) }
        safeIRStorageAllocationState (.intLit 0) = .ok (.int 0) := by simp [evalExpr?, pure]
    have hb₄ := pureConsTail (fun _ hs ↦ letResult he₂ hs) hb₃
    have hl := safeStorageAtInitialLocals ⟨0⟩ safeIRStorageAllocationLength
    cases hb₄ with
    | consNormal hloop ht =>
      obtain ⟨ls, ws, he, hls⟩ := storageLoopResult safeIRStorageAllocationState hl
        (fuel := safeIRStorageAllocationLength.toNat) (by simp) hloop
      cases he
      exact storageReturnCannotRevert hls ht
    | consRevert hloop =>
      obtain ⟨_, _, he, _⟩ := storageLoopResult safeIRStorageAllocationState hl
        (fuel := safeIRStorageAllocationLength.toNat) (by simp) hloop
      cases he

theorem safeIRStorageAllocationNotRefines :
    ¬runtimeRefinementFor config contract safeIRStorageAllocationAccounts
      safeIRStorageAllocationAccounts ⟨100000⟩ default safeIRStorageAllocationEnv := by
  intro h
  have hex := safeIRStorageAllocationExecution
  have hsel := safeIRStorageAllocationPremises.2.2.2
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
        rw [safeIRStorageAllocationDecoding] at hdec
        cases hdec
        cases hstate
        exact safeIRStorageAllocationSourceCannotRevert hbody
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
    rw [safeIRStorageAllocationDecoding] at hdec
    cases hdec
  | outOfGas hevm => rw [hevm] at hex; cases hex

-- The local guard proposed for getStorageAt includes its 128-byte starting pointer and header.
theorem safeIRStorageAllocationCorrectedBound (bytes : Nat) :
    bytes + 160 ≤ 2 ^ 64 - 1 ↔ bytes ≤ 2 ^ 64 - 161 := by omega

theorem safeIRStorageAllocationRejectedByCorrectedBound :
    ¬(UInt256.shiftLeft safeIRStorageAllocationLength (UInt256.ofNat 5)).toNat ≤
      2 ^ 64 - 161 := by decide

end Benchmarks.Safe.ViaIR
