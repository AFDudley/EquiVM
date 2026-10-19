import Solidity.Interp.Sound
import Solidity.Interp.Complete
import Solidity.Refine.Behaviors

/-!
# Entry points: soundness and completeness

`interpExec` / `interpCtor` results are derivable by `solidityExec` / `solidityCtorExec`, and the
boolean rejection test implies the relation's rejection predicate.


Completeness of the entry points (`interpExec`, `interpCtor`), the `iff` characterisations of
`solidityExec` / `solidityCtorExec` by the interpreter, and determinism of the relations.
-/

namespace Solidity

open Interp

variable {cfg : Config} {o : Oracle} {fc : FlatContract}

theorem payableOrNoValue_of {d : FnDecl} {I : Ethereum.ExecutionEnv}
    (h : ¬ (d.mutability != .payable && I.weiValue != ⟨0⟩) = true) : payableOrNoValue d I := by
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and, not_not] at h
  unfold payableOrNoValue
  by_cases hp : d.mutability = .payable
  · exact Or.inl hp
  · exact Or.inr (h hp)

theorem interpExec_sound {fuel immutables σ σ₀ g A I res conv}
    (h : (interpExec cfg o fc fuel immutables σ σ₀ g A I).run = some (.ok (res, conv))) :
    solidityExec cfg o fc immutables σ σ₀ g A I res conv := by
  simp only [interpExec] at h
  split at h
  · -- a selector matched
    rename_i e he
    rcases IM.bind_some h with ⟨d, hd, hr⟩ | ⟨fn, hfn, h⟩ <;> try dsimp only at h
    · exact (liftOpt_error hd).elim
    · rcases IM.bind_some h with ⟨d, hd, hr⟩ | ⟨retTys, hret, h⟩ <;> try dsimp only at h
      · exact (liftOpt_error hd).elim
      · split at h
        · rename_i hnp
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hnp
          cases IM.pure_some h
          exact .nonPayable he (liftOpt_ok hfn) hnp.1 hnp.2 (liftOpt_ok hret)
        · rename_i hnp
          have hpay := payableOrNoValue_of hnp
          have h := IM.pure_bind_some h
          try dsimp only at h
          rcases IM.bind_some h with ⟨d, hd, hr⟩ | ⟨svs, hsvs, h⟩ <;> try dsimp only at h
          · exact (liftOpt_error hd).elim
          · rcases IM.bind_some h with ⟨d, hd, hr⟩ | ⟨⟨vs, h0⟩, hvs, h⟩ <;> try dsimp only at h
            · exact (liftOpt_error hd).elim
            · split at h
              · rename_i rets m' hcall
                have hc := callFn_sound (cfg := cfg) (o := o) (fc := fc) hcall
                split at h
                · rename_i rets' h' hprep
                  rcases IM.bind_some h with ⟨d, hd, hr⟩ | ⟨out, hout, h⟩ <;> try dsimp only at h
                  · exact (liftOpt_error hd).elim
                  · cases IM.pure_some h
                    exact .call he (liftOpt_ok hfn) hpay (liftOpt_ok hret) (liftOpt_ok hsvs) (liftOpt_ok hvs) hc hprep (liftOpt_ok hout)
                · rename_i p hprep
                  cases IM.pure_some h
                  exact .callReturnPanic he (liftOpt_ok hfn) hpay (liftOpt_ok hret) (liftOpt_ok hsvs) (liftOpt_ok hvs) hc hprep
                · simp at h
              · rename_i m' d hcall
                have hc := callFn_sound (cfg := cfg) (o := o) (fc := fc) hcall
                cases IM.pure_some h
                exact .callHalted he (liftOpt_ok hfn) hpay (liftOpt_ok hret) (liftOpt_ok hsvs) (liftOpt_ok hvs) hc
              · rename_i d hcall
                have hc := callFn_sound (cfg := cfg) (o := o) (fc := fc) hcall
                cases IM.pure_some h
                exact .callReverted he (liftOpt_ok hfn) hpay (liftOpt_ok hret) (liftOpt_ok hsvs) (liftOpt_ok hvs) hc
              · simp at h
  · -- no selector
    rename_i he
    split at h
    · rename_i hrec
      simp only [Bool.and_eq_true, beq_iff_eq, Option.isSome_iff_exists] at hrec
      rcases IM.bind_some h with ⟨d, hd, hr⟩ | ⟨fid, hfid, h⟩ <;> try dsimp only at h
      · exact (liftOpt_error hd).elim
      · rcases IM.bind_some h with ⟨d, hd, hr⟩ | ⟨fn, hfn, h⟩ <;> try dsimp only at h
        · exact (liftOpt_error hd).elim
        · split at h
          · rename_i rets m' hcall
            have hc := callFn_sound (cfg := cfg) (o := o) (fc := fc) hcall
            cases IM.pure_some h
            exact .receive hrec.1 (liftOpt_ok hfid) (liftOpt_ok hfn) hc
          · rename_i m' d hcall
            have hc := callFn_sound (cfg := cfg) (o := o) (fc := fc) hcall
            cases IM.pure_some h
            exact .receiveHalted hrec.1 (liftOpt_ok hfid) (liftOpt_ok hfn) hc
          · rename_i d hcall
            have hc := callFn_sound (cfg := cfg) (o := o) (fc := fc) hcall
            cases IM.pure_some h
            exact .receiveReverted hrec.1 (liftOpt_ok hfid) (liftOpt_ok hfn) hc
          · simp at h
    · rename_i hrec
      have hrec' : fc.receive? = none ∨ I.calldata.size ≠ 0 := by
        simp only [Bool.and_eq_true, beq_iff_eq, not_and, Option.isSome_iff_ne_none] at hrec
        by_cases hs : I.calldata.size = 0
        · exact Or.inl (by_contra fun hn => hrec hs hn)
        · exact Or.inr hs
      rcases IM.bind_some h with ⟨d, hd, hr⟩ | ⟨fid, hfid, h⟩ <;> try dsimp only at h
      · exact (liftOpt_error hd).elim
      · rcases IM.bind_some h with ⟨d, hd, hr⟩ | ⟨fn, hfn, h⟩ <;> try dsimp only at h
        · exact (liftOpt_error hd).elim
        · split at h
          · rename_i hnp
            simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hnp
            cases IM.pure_some h
            exact .fallbackNonPayable he hrec' (liftOpt_ok hfid) (liftOpt_ok hfn) hnp.1 hnp.2
          · rename_i hnp
            have hpay := payableOrNoValue_of hnp
            have h := IM.pure_bind_some h
            try dsimp only at h
            rcases IM.bind_some h with ⟨d, hd, hr⟩ | ⟨⟨vs, h0⟩, hvs, h⟩ <;> try dsimp only at h
            · exact (liftOpt_error hd).elim
            · split at h
              · rename_i rets m' hcall
                have hc := callFn_sound (cfg := cfg) (o := o) (fc := fc) hcall
                rcases IM.bind_some h with ⟨d, hd, hr⟩ | ⟨out, hout, h⟩ <;> try dsimp only at h
                · exact (liftOpt_error hd).elim
                · cases IM.pure_some h
                  exact .fallback he hrec' (liftOpt_ok hfid) (liftOpt_ok hfn) hpay (liftOpt_ok hvs) hc (liftOpt_ok hout)
              · rename_i m' d hcall
                have hc := callFn_sound (cfg := cfg) (o := o) (fc := fc) hcall
                cases IM.pure_some h
                exact .fallbackHalted he hrec' (liftOpt_ok hfid) (liftOpt_ok hfn) hpay (liftOpt_ok hvs) hc
              · rename_i d hcall
                have hc := callFn_sound (cfg := cfg) (o := o) (fc := fc) hcall
                cases IM.pure_some h
                exact .fallbackReverted he hrec' (liftOpt_ok hfid) (liftOpt_ok hfn) hpay (liftOpt_ok hvs) hc
              · simp at h

/-- The boolean rejection test implies the relation's rejection predicate. -/
theorem specRejectsB_sound {I : Ethereum.ExecutionEnv} (h : specRejectsB cfg fc I = true) : specRejects cfg fc I := by
  unfold specRejectsB at h
  split at h
  · rename_i hd
    exact Or.inl (by simpa using hd)
  · rename_i hd
    split at h
    · rename_i e he
      split at h
      · rename_i fn hfn
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h
        exact Or.inr ⟨e, fn, he, hfn, h.1, h.2⟩
      · simp at h
    · simp at h

/-! ## Construction -/

def ctorOf : Except ByteArray CtorResult → CtorResult
  | .ok r => r
  | .error d => .reverted d

def chainOf : Except ByteArray (Machine × Store) → CtorResult
  | .ok (m, imms) => .ok m imms
  | .error d => .reverted d

theorem initsFold_sound (fuel : Nat) : ∀ (vs : List FlatVar) fr m r,
    (vs.foldlM (initStep cfg o fc fuel) (fr, m)).run = some r → ExecInits cfg o fc fr m vs (unitResOf r)
  | [], fr, m, r, h => by
    simp only [List.foldlM_nil] at h
    cases IM.pure_some h; exact .nil
  | v :: vs, fr, m, r, h => by
    simp only [List.foldlM_cons] at h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨fr1, m1⟩, hstep, h⟩ <;> try dsimp only at h
    · -- the step reverted
      simp only [initStep] at hd
      split at hd
      · rename_i e he
        rcases IM.bind_some hd with ⟨d', hd', hdd⟩ | ⟨⟨val, fr1, m1⟩, hval, hd⟩ <;> try dsimp only at hd
        · cases hdd; exact .revert he (evalExpr_sound hd')
        · split at hd
          · rename_i hmut
            obtain ⟨p, hp, hpd⟩ := liftOp_error hd
            cases hpd; exact .storagePanic hmut he (evalExpr_sound hval) hp
          · rename_i hmut
            obtain ⟨p, hp, hpd⟩ := liftOp_error hd
            cases hpd; exact .immutablePanic hmut he (evalExpr_sound hval) hp
          · simp at hd
      · simp at hd
    · simp only [initStep] at hstep
      split at hstep
      · rename_i e he
        rcases IM.bind_some hstep with ⟨d', hd', hdd⟩ | ⟨⟨val, fr1', m1'⟩, hval, hstep⟩ <;> try dsimp only at hstep
        · cases hdd
        · split at hstep
          · rename_i hmut
            exact .storage hmut he (evalExpr_sound hval) (liftOp_ok hstep) (initsFold_sound fuel vs _ _ _ h)
          · rename_i hmut
            exact .immutable hmut he (evalExpr_sound hval) (liftOp_ok hstep) (initsFold_sound fuel vs _ _ _ h)
          · simp at hstep
      · simp at hstep

theorem ctorArgs_sound {fuel topArgs imms tbl m step vs m1}
    (h : (ctorArgsOf cfg o fc fuel topArgs imms tbl m step).run = some (.ok (vs, m1))) :
    ∃ fr', CtorArgs cfg o fc topArgs imms tbl m step (.ok vs fr' m1) := by
  simp only [ctorArgsOf] at h
  split at h
  · rename_i hc
    cases IM.pure_some h
    exact ⟨_, .top (by simpa using hc)⟩
  · rename_i hc
    have hc' : step.contract ≠ fc.name := by simpa using hc
    split at h
    · rename_i hargs
      cases IM.pure_some h
      exact ⟨_, .none hc' hargs⟩
    · rename_i w a hargs
      rcases IM.bind_some h with ⟨d, hd, hdd⟩ | ⟨wvs, hw, h⟩ <;> try dsimp only at h
      · exact (liftOpt_error hd).elim
      · rcases IM.bind_some h with ⟨d, hd, hdd⟩ | ⟨⟨frW, mW⟩, hfr, h⟩ <;> try dsimp only at h
        · cases hdd
        · rcases IM.bind_some h with ⟨d, hd, hdd⟩ | ⟨es, hes, h⟩ <;> try dsimp only at h
          · exact (liftOpt_error hd).elim
          · rcases IM.bind_some h with ⟨d, hd, hdd⟩ | ⟨⟨vs', fr', m1'⟩, hvs, h⟩ <;> try dsimp only at h
            · cases hdd
            · cases IM.pure_some h
              exact ⟨fr', .some hc' hargs (liftOpt_ok hw) (liftOp_ok hfr) (liftOpt_ok hes)
                ((soundAt cfg o fc fuel).exprs _ _ _ _ hvs)⟩

theorem ctorArgs_revert {fuel topArgs imms tbl m step d}
    (h : (ctorArgsOf cfg o fc fuel topArgs imms tbl m step).run = some (.error d)) :
    CtorArgs cfg o fc topArgs imms tbl m step (.reverted d) := by
  simp only [ctorArgsOf] at h
  split at h
  · cases IM.pure_some h
  · rename_i hc
    have hc' : step.contract ≠ fc.name := by simpa using hc
    split at h
    · cases IM.pure_some h
    · rename_i w a hargs
      rcases IM.bind_some h with ⟨d', hd, hdd⟩ | ⟨wvs, hw, h⟩ <;> try dsimp only at h
      · exact (liftOpt_error hd).elim
      · rcases IM.bind_some h with ⟨d', hd, hdd⟩ | ⟨⟨frW, mW⟩, hfr, h⟩ <;> try dsimp only at h
        · obtain ⟨p, hp, hpd⟩ := liftOp_error hd
          cases hdd; cases hpd; exact .framePanic hc' hargs (liftOpt_ok hw) hp
        · rcases IM.bind_some h with ⟨d', hd, hdd⟩ | ⟨es, hes, h⟩ <;> try dsimp only at h
          · exact (liftOpt_error hd).elim
          · rcases IM.bind_some h with ⟨d', hd, hdd⟩ | ⟨⟨vs', fr', m1'⟩, hvs, h⟩ <;> try dsimp only at h
            · cases hdd
              exact .some hc' hargs (liftOpt_ok hw) (liftOp_ok hfr) (liftOpt_ok hes)
                ((soundAt cfg o fc fuel).exprs _ _ _ _ hd)
            · cases IM.pure_some h

theorem argsFold_sound (fuel : Nat) (topArgs : List Value) (imms : Store) : ∀ (steps : List CtorStep) tbl m r,
    (steps.foldlM (argsStep cfg o fc fuel topArgs imms) (tbl, m)).run = some r →
      CtorArgsAll cfg o fc topArgs imms tbl m steps r
  | [], tbl, m, r, h => by
    simp only [List.foldlM_nil] at h
    cases IM.pure_some h; exact .nil
  | step :: steps, tbl, m, r, h => by
    simp only [List.foldlM_cons] at h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨tbl', m'⟩, hstep, h⟩ <;> try dsimp only at h
    · simp only [argsStep] at hd
      rcases IM.bind_some hd with ⟨d', hd', hdd⟩ | ⟨⟨vs, m1⟩, hargs, hd⟩ <;> try dsimp only at hd
      · cases hdd; exact .revert (ctorArgs_revert hd')
      · cases IM.pure_some hd
    · simp only [argsStep] at hstep
      rcases IM.bind_some hstep with ⟨d', hd', hdd⟩ | ⟨⟨vs, m1⟩, hargs, hstep⟩ <;> try dsimp only at hstep
      · cases hdd
      · cases IM.pure_some hstep
        obtain ⟨fr', hca⟩ := ctorArgs_sound hargs
        exact .cons hca (argsFold_sound fuel topArgs imms steps _ _ _ h)

theorem chainFold_sound (fuel : Nat) (tbl : List (Ident × List Value)) : ∀ (steps : List CtorStep) m imms r,
    (steps.foldlM (ctorStep cfg o fc fuel tbl) (m, imms)).run = some r →
      ExecCtorChain cfg o fc tbl imms m steps (chainOf r)
  | [], m, imms, r, h => by
    simp only [List.foldlM_nil] at h
    cases IM.pure_some h; exact .nil
  | step :: steps, m, imms, r, h => by
    simp only [List.foldlM_cons] at h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨m', imms'⟩, hstep, h⟩ <;> try dsimp only at h
    · simp only [ctorStep] at hd
      split at hd
      · cases IM.pure_some hd
      · rename_i fid hfid
        rcases IM.bind_some hd with ⟨d', hd', hdd⟩ | ⟨fn, hfn, hd⟩ <;> try dsimp only at hd
        · exact (liftOpt_error hd').elim
        · rcases IM.bind_some hd with ⟨d', hd', hdd⟩ | ⟨vs, hvs, hd⟩ <;> try dsimp only at hd
          · exact (liftOpt_error hd').elim
          · rcases IM.bind_some hd with ⟨d', hd', hdd⟩ | ⟨⟨fr2, m2⟩, henter, hd⟩ <;> try dsimp only at hd
            · obtain ⟨p, hp, hpd⟩ := liftOp_error hd'
              cases hdd; cases hpd; exact .enterPanic hfid (liftOpt_ok hfn) (liftOpt_ok hvs) hp
            · split at hd
              · rename_i body hbody
                rcases IM.bind_some hd with ⟨d', hd', hdd⟩ | ⟨r', hr, hd⟩ <;> try dsimp only at hd
                · cases hdd
                  exact .bodyReverted hfid (liftOpt_ok hfn) (liftOpt_ok hvs) (liftOp_ok henter) hbody
                    ((soundAt cfg o fc fuel).chain _ _ _ _ _ hd')
                · rcases IM.bind_some hd with ⟨d', hd', hdd⟩ | ⟨⟨fr4, m4⟩, hfin, hd⟩ <;> try dsimp only at hd
                  · exact (liftOpt_error hd').elim
                  · cases IM.pure_some hd
              · simp at hd
    · simp only [ctorStep] at hstep
      split at hstep
      · cases IM.pure_some hstep
        exact .skip ‹_› (chainFold_sound fuel tbl steps _ _ _ h)
      · rename_i fid hfid
        rcases IM.bind_some hstep with ⟨d', hd', hdd⟩ | ⟨fn, hfn, hstep⟩ <;> try dsimp only at hstep
        · cases hdd
        · rcases IM.bind_some hstep with ⟨d', hd', hdd⟩ | ⟨vs, hvs, hstep⟩ <;> try dsimp only at hstep
          · cases hdd
          · rcases IM.bind_some hstep with ⟨d', hd', hdd⟩ | ⟨⟨fr2, m2⟩, henter, hstep⟩ <;> try dsimp only at hstep
            · cases hdd
            · split at hstep
              · rename_i body hbody
                rcases IM.bind_some hstep with ⟨d', hd', hdd⟩ | ⟨r', hr, hstep⟩ <;> try dsimp only at hstep
                · cases hdd
                · rcases IM.bind_some hstep with ⟨d', hd', hdd⟩ | ⟨⟨fr4, m4⟩, hfin, hstep⟩ <;> try dsimp only at hstep
                  · exact (liftOpt_error hd').elim
                  · cases IM.pure_some hstep
                    exact .run hfid (liftOpt_ok hfn) (liftOpt_ok hvs) (liftOp_ok henter) hbody
                      ((soundAt cfg o fc fuel).chain _ _ _ _ _ hr) (liftOpt_ok hfin)
                      (chainFold_sound fuel tbl steps _ _ _ h)
              · simp at hstep

theorem ctorPayableB_iff {I : Ethereum.ExecutionEnv} : ctorPayableB fc I = true ↔ ctorPayable fc I := by
  unfold ctorPayableB ctorPayable
  split <;> rename_i heq <;> simp [heq]

theorem interpCtor_sound {fuel args σ σ₀ g A I r}
    (h : (interpCtor cfg o fc fuel args σ σ₀ g A I).run = some r) :
    solidityCtorExec cfg o fc args σ σ₀ g A I (ctorOf r) := by
  simp only [interpCtor] at h
  split at h
  · rename_i hnp
    cases IM.pure_some h
    exact .nonPayable (fun hpay => by simp [ctorPayableB_iff.mpr hpay] at hnp)
  · rename_i hp
    have hpay : ctorPayable fc I := ctorPayableB_iff.mp (by simpa using hp)
    have h := IM.pure_bind_some h
    try dsimp only at h
    rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨imms0, himms, h⟩ <;> try dsimp only at h
    · exact (liftOpt_error hd).elim
    · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨topArgs, h0⟩, hargs, h⟩ <;> try dsimp only at h
      · exact (liftOpt_error hd).elim
      · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨frI, m1⟩, hinits, h⟩ <;> try dsimp only at h
        · exact .initsReverted hpay (liftOpt_ok himms) (liftOpt_ok hargs) (initsFold_sound fuel _ _ _ _ hd)
        · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨tbl, m2⟩, hav, h⟩ <;> try dsimp only at h
          · exact .argsReverted hpay (liftOpt_ok himms) (liftOpt_ok hargs) (initsFold_sound fuel _ _ _ _ hinits)
              (argsFold_sound fuel _ _ _ _ _ _ hd)
          · rcases IM.bind_some h with ⟨d, hd, rfl⟩ | ⟨⟨m3, imms⟩, hchain, h⟩ <;> try dsimp only at h
            · exact .run hpay (liftOpt_ok himms) (liftOpt_ok hargs) (initsFold_sound fuel _ _ _ _ hinits)
                (argsFold_sound fuel _ _ _ _ _ _ hav) (chainFold_sound fuel _ _ _ _ _ hd)
            · cases IM.pure_some h
              exact .run hpay (liftOpt_ok himms) (liftOpt_ok hargs) (initsFold_sound fuel _ _ _ _ hinits)
                (argsFold_sound fuel _ _ _ _ _ _ hav) (chainFold_sound fuel _ _ _ _ _ hchain)


/-! ## Boolean forms of the payability guards -/

theorem payableOrNoValue_false {d : FnDecl} {I : Ethereum.ExecutionEnv} (h : payableOrNoValue d I) :
    (d.mutability != .payable && I.weiValue != ⟨0⟩) = false := by
  unfold payableOrNoValue at h
  rcases h with h | h <;> simp [h]

theorem nonPayable_true {d : FnDecl} {I : Ethereum.ExecutionEnv} (h1 : d.mutability ≠ .payable)
    (h2 : I.weiValue ≠ ⟨0⟩) : (d.mutability != .payable && I.weiValue != ⟨0⟩) = true := by
  simp [h1, h2]

theorem selectorDispatch_empty {calldata : ByteArray} (h : calldata.size = 0) :
    selectorDispatch fc calldata = none := by
  simp [selectorDispatch, h]

theorem noReceive_false {I : Ethereum.ExecutionEnv} (h : fc.receive? = none ∨ I.calldata.size ≠ 0) :
    (I.calldata.size == 0 && fc.receive?.isSome) = false := by
  rcases h with h | h <;> simp [h]

theorem ctorPayableB_false {I : Ethereum.ExecutionEnv} (h : ¬ ctorPayable fc I) : ctorPayableB fc I = false := by
  cases hb : ctorPayableB fc I
  · rfl
  · exact absurd (ctorPayableB_iff.mp hb) h

/-! ## Completeness of the message-call entry point -/

theorem interpExec_complete {immutables σ σ₀ g A I res conv}
    (h : solidityExec cfg o fc immutables σ σ₀ g A I res conv) :
    ∃ n, ∀ k, n ≤ k → (interpExec cfg o fc k immutables σ σ₀ g A I).run = some (.ok (res, conv)) := by
  cases h with
  | call he hfn hpay hret hsvs hvs hc hprep hout =>
    obtain ⟨n, ih⟩ := callFn_complete hc
    refine ⟨n, fun k hk => ?_⟩
    have ih' : callFn cfg o fc k (rootFrame fc) (initMachine σ σ₀ g A I immutables _) _ _ = some (.ok (.ok _ _)) := ih k hk
    interp_simp [interpExec, he, hfn, hret, hsvs, hvs, hprep, hout, ih', payableOrNoValue_false hpay]
  | callReturnPanic he hfn hpay hret hsvs hvs hc hprep =>
    obtain ⟨n, ih⟩ := callFn_complete hc
    refine ⟨n, fun k hk => ?_⟩
    have ih' : callFn cfg o fc k (rootFrame fc) (initMachine σ σ₀ g A I immutables _) _ _ = some (.ok (.ok _ _)) := ih k hk
    interp_simp [interpExec, he, hfn, hret, hsvs, hvs, hprep, ih', payableOrNoValue_false hpay]
  | callReverted he hfn hpay hret hsvs hvs hc =>
    obtain ⟨n, ih⟩ := callFn_complete hc
    refine ⟨n, fun k hk => ?_⟩
    have ih' : callFn cfg o fc k (rootFrame fc) (initMachine σ σ₀ g A I immutables _) _ _ = some (.error _) := ih k hk
    interp_simp [interpExec, he, hfn, hret, hsvs, hvs, ih', payableOrNoValue_false hpay]
  | callHalted he hfn hpay hret hsvs hvs hc =>
    obtain ⟨n, ih⟩ := callFn_complete hc
    refine ⟨n, fun k hk => ?_⟩
    have ih' : callFn cfg o fc k (rootFrame fc) (initMachine σ σ₀ g A I immutables _) _ _ = some (.ok (.halted _ _)) := ih k hk
    interp_simp [interpExec, he, hfn, hret, hsvs, hvs, ih', payableOrNoValue_false hpay]
  | nonPayable he hfn h1 h2 hret =>
    refine ⟨0, fun k _ => ?_⟩
    interp_simp [interpExec, he, hfn, hret, nonPayable_true h1 h2]
  | receive hsz hrec hfn hc =>
    obtain ⟨n, ih⟩ := callFn_complete hc
    refine ⟨n, fun k hk => ?_⟩
    have ih' : callFn cfg o fc k (rootFrame fc) (initMachine σ σ₀ g A I immutables) _ [] = some (.ok (.ok _ _)) := ih k hk
    interp_simp [interpExec, selectorDispatch_empty hsz, hsz, hrec, hfn, ih']
  | receiveReverted hsz hrec hfn hc =>
    obtain ⟨n, ih⟩ := callFn_complete hc
    refine ⟨n, fun k hk => ?_⟩
    have ih' : callFn cfg o fc k (rootFrame fc) (initMachine σ σ₀ g A I immutables) _ [] = some (.error _) := ih k hk
    interp_simp [interpExec, selectorDispatch_empty hsz, hsz, hrec, hfn, ih']
  | receiveHalted hsz hrec hfn hc =>
    obtain ⟨n, ih⟩ := callFn_complete hc
    refine ⟨n, fun k hk => ?_⟩
    have ih' : callFn cfg o fc k (rootFrame fc) (initMachine σ σ₀ g A I immutables) _ [] = some (.ok (.halted _ _)) := ih k hk
    interp_simp [interpExec, selectorDispatch_empty hsz, hsz, hrec, hfn, ih']
  | fallbackHalted he hrec hfb hfn hpay hargs hc =>
    obtain ⟨n, ih⟩ := callFn_complete hc
    refine ⟨n, fun k hk => ?_⟩
    have ih' : callFn cfg o fc k (rootFrame fc) (initMachine σ σ₀ g A I immutables _) _ _ = some (.ok (.halted _ _)) := ih k hk
    interp_simp [interpExec, he, noReceive_false hrec, hfb, hfn, hargs, ih', payableOrNoValue_false hpay]
  | fallback he hrec hfb hfn hpay hargs hc hout =>
    obtain ⟨n, ih⟩ := callFn_complete hc
    refine ⟨n, fun k hk => ?_⟩
    have ih' : callFn cfg o fc k (rootFrame fc) (initMachine σ σ₀ g A I immutables _) _ _ = some (.ok (.ok _ _)) := ih k hk
    interp_simp [interpExec, he, noReceive_false hrec, hfb, hfn, hargs, hout, ih', payableOrNoValue_false hpay]
  | fallbackReverted he hrec hfb hfn hpay hargs hc =>
    obtain ⟨n, ih⟩ := callFn_complete hc
    refine ⟨n, fun k hk => ?_⟩
    have ih' : callFn cfg o fc k (rootFrame fc) (initMachine σ σ₀ g A I immutables _) _ _ = some (.error _) := ih k hk
    interp_simp [interpExec, he, noReceive_false hrec, hfb, hfn, hargs, ih', payableOrNoValue_false hpay]
  | fallbackNonPayable he hrec hfb hfn h1 h2 =>
    refine ⟨0, fun k _ => ?_⟩
    interp_simp [interpExec, he, noReceive_false hrec, hfb, hfn, nonPayable_true h1 h2]

/-! ## Completeness of construction -/

def toArgs : Res (List Value) → Except ByteArray (List Value × Machine)
  | .ok vs _ m => .ok (vs, m)
  | .reverted d => .error d

def toChain : CtorResult → Except ByteArray (Machine × Store)
  | .ok m imms => .ok (m, imms)
  | .reverted d => .error d

/-- A finished body is not a revert. -/
theorem toExec_of_finished {r : ExecResult} {fr : Frame} {m : Machine} (h : finished r = some (fr, m)) :
    toExec r = .ok r := by
  cases r <;> simp_all [finished, toExec]

theorem initsFold_complete {fr m vs r} (h : ExecInits cfg o fc fr m vs r) :
    ∃ n, ∀ k, n ≤ k → (vs.foldlM (initStep cfg o fc k) (fr, m)).run = some (toUnit r) := by
  induction h with
  | nil => exact ⟨0, fun k _ => by simp⟩
  | storage hmut hinit hev hassign _ ih =>
    obtain ⟨n1, ih1⟩ := evalExpr_complete hev
    obtain ⟨n2, ih2⟩ := ih
    refine ⟨n1 + n2, fun k hk => ?_⟩
    interp_simp [List.foldlM_cons, initStep, hmut, hinit, hassign, ih1 k (by omega), ih2 k (by omega)]
  | immutable hmut hinit hev hassign _ ih =>
    obtain ⟨n1, ih1⟩ := evalExpr_complete hev
    obtain ⟨n2, ih2⟩ := ih
    refine ⟨n1 + n2, fun k hk => ?_⟩
    interp_simp [List.foldlM_cons, initStep, hmut, hinit, hassign, ih1 k (by omega), ih2 k (by omega)]
  | revert hinit hev =>
    obtain ⟨n1, ih1⟩ := evalExpr_complete hev
    refine ⟨n1, fun k hk => ?_⟩
    interp_simp [List.foldlM_cons, initStep, hinit, ih1 k hk]
  | storagePanic hmut hinit hev hassign =>
    obtain ⟨n1, ih1⟩ := evalExpr_complete hev
    refine ⟨n1, fun k hk => ?_⟩
    interp_simp [List.foldlM_cons, initStep, hmut, hinit, hassign, ih1 k hk]
  | immutablePanic hmut hinit hev hassign =>
    obtain ⟨n1, ih1⟩ := evalExpr_complete hev
    refine ⟨n1, fun k hk => ?_⟩
    interp_simp [List.foldlM_cons, initStep, hmut, hinit, hassign, ih1 k hk]

theorem ctorArgs_complete {topArgs imms tbl m step r} (h : CtorArgs cfg o fc topArgs imms tbl m step r) :
    ∃ n, ∀ k, n ≤ k → (ctorArgsOf cfg o fc k topArgs imms tbl m step).run = some (toArgs r) := by
  cases h with
  | top hc =>
    refine ⟨0, fun k _ => ?_⟩
    interp_simp [ctorArgsOf, toArgs, hc]
  | none hc hargs =>
    refine ⟨0, fun k _ => ?_⟩
    interp_simp [ctorArgsOf, toArgs, hc, hargs]
  | some hc hargs hw hfr hes hev =>
    obtain ⟨n, ih⟩ := evalExprs_complete hev
    refine ⟨n, fun k hk => ?_⟩
    rcases r with ⟨vs, fr', m1⟩ | d <;> interp_simp [ctorArgsOf, toArgs, hc, hargs, hw, hfr, hes, ih k hk]
  | framePanic hc hargs hw hfr =>
    refine ⟨0, fun k _ => ?_⟩
    interp_simp [ctorArgsOf, toArgs, hc, hargs, hw, hfr]

theorem argsFold_complete {topArgs imms tbl m steps r} (h : CtorArgsAll cfg o fc topArgs imms tbl m steps r) :
    ∃ n, ∀ k, n ≤ k → (steps.foldlM (argsStep cfg o fc k topArgs imms) (tbl, m)).run = some r := by
  induction h with
  | nil => exact ⟨0, fun k _ => by simp⟩
  | cons hca _ ih =>
    obtain ⟨na, iha⟩ := ctorArgs_complete hca
    obtain ⟨nr, ihr⟩ := ih
    refine ⟨na + nr, fun k hk => ?_⟩
    interp_simp [List.foldlM_cons, argsStep, toArgs, iha k (by omega), ihr k (by omega)]
  | revert hca =>
    obtain ⟨na, iha⟩ := ctorArgs_complete hca
    refine ⟨na, fun k hk => ?_⟩
    interp_simp [List.foldlM_cons, argsStep, toArgs, iha k hk]

theorem chainFold_complete {tbl imms m steps r} (h : ExecCtorChain cfg o fc tbl imms m steps r) :
    ∃ n, ∀ k, n ≤ k → (steps.foldlM (ctorStep cfg o fc k tbl) (m, imms)).run = some (toChain r) := by
  induction h with
  | nil => exact ⟨0, fun k _ => by simp [toChain]⟩
  | skip hfn _ ih =>
    obtain ⟨n, ihn⟩ := ih
    refine ⟨n, fun k hk => ?_⟩
    interp_simp [List.foldlM_cons, ctorStep, hfn, ihn k hk]
  | run hfid hfn hvs henter hbody hchain hfin _ ih =>
    obtain ⟨nc, ihc⟩ := execChain_complete hchain
    obtain ⟨nr, ihr⟩ := ih
    refine ⟨nc + nr, fun k hk => ?_⟩
    have ihc' := ihc k (by omega)
    rw [toExec_of_finished hfin] at ihc'
    interp_simp [List.foldlM_cons, ctorStep, toChain, hfid, hfn, hvs, henter, hbody, hfin, ihc', ihr k (by omega)]
  | bodyReverted hfid hfn hvs henter hbody hchain =>
    obtain ⟨nc, ihc⟩ := execChain_complete hchain
    refine ⟨nc, fun k hk => ?_⟩
    interp_simp [List.foldlM_cons, ctorStep, toChain, hfid, hfn, hvs, henter, hbody, ihc k (by omega)]
  | enterPanic hfid hfn hvs henter =>
    refine ⟨0, fun k _ => ?_⟩
    interp_simp [List.foldlM_cons, ctorStep, toChain, hfid, hfn, hvs, henter]

theorem interpCtor_complete {args σ σ₀ g A I r}
    (h : solidityCtorExec cfg o fc args σ σ₀ g A I r) :
    ∃ n, ∀ k, n ≤ k → ((interpCtor cfg o fc k args σ σ₀ g A I).run).map ctorOf = some r := by
  cases h with
  | run hpay himms hargs hinits hav hchain =>
    obtain ⟨ni, ihi⟩ := initsFold_complete hinits
    obtain ⟨na, iha⟩ := argsFold_complete hav
    obtain ⟨nc, ihc⟩ := chainFold_complete hchain
    refine ⟨ni + na + nc, fun k hk => ?_⟩
    rcases r with ⟨m3, imms⟩ | d <;>
      interp_simp [interpCtor, ctorOf, toChain, ctorPayableB_iff.mpr hpay, himms, hargs, ihi k (by omega),
        iha k (by omega), ihc k (by omega), Option.map_some]
  | initsReverted hpay himms hargs hinits =>
    obtain ⟨ni, ihi⟩ := initsFold_complete hinits
    refine ⟨ni, fun k hk => ?_⟩
    interp_simp [interpCtor, ctorOf, ctorPayableB_iff.mpr hpay, himms, hargs, ihi k hk, Option.map_some]
  | argsReverted hpay himms hargs hinits hav =>
    obtain ⟨ni, ihi⟩ := initsFold_complete hinits
    obtain ⟨na, iha⟩ := argsFold_complete hav
    refine ⟨ni + na, fun k hk => ?_⟩
    interp_simp [interpCtor, ctorOf, ctorPayableB_iff.mpr hpay, himms, hargs, ihi k (by omega), iha k (by omega),
      Option.map_some]
  | nonPayable hnp =>
    refine ⟨0, fun k _ => ?_⟩
    interp_simp [interpCtor, ctorOf, ctorPayableB_false hnp, Option.map_some]

/-! ## The relations are exactly what the interpreter computes -/

theorem solidityExec_iff {immutables σ σ₀ g A I res conv} :
    solidityExec cfg o fc immutables σ σ₀ g A I res conv ↔
      ∃ k, (interpExec cfg o fc k immutables σ σ₀ g A I).run = some (.ok (res, conv)) :=
  ⟨fun h => let ⟨n, hn⟩ := interpExec_complete h; ⟨n, hn n (Nat.le_refl n)⟩, fun ⟨_, hk⟩ => interpExec_sound hk⟩

theorem solidityCtorExec_iff {args σ σ₀ g A I r} :
    solidityCtorExec cfg o fc args σ σ₀ g A I r ↔
      ∃ k, ((interpCtor cfg o fc k args σ σ₀ g A I).run).map ctorOf = some r := by
  refine ⟨fun h => let ⟨n, hn⟩ := interpCtor_complete h; ⟨n, hn n (Nat.le_refl n)⟩, fun ⟨k, hk⟩ => ?_⟩
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hk
  exact interpCtor_sound hx

theorem evalExpr_iff {fr m e r} :
    EvalExpr cfg o fc fr m e r ↔ ∃ k, (evalExpr cfg o fc k fr m e).run = some (toRes r) :=
  ⟨fun h => let ⟨n, hn⟩ := evalExpr_complete h; ⟨n, hn n (Nat.le_refl n)⟩,
   fun ⟨k, hk⟩ => by cases r <;> exact evalExpr_sound hk⟩

theorem execStmt_iff {fr m s r} :
    ExecStmt cfg o fc fr m s r ↔ ∃ k, (execStmt cfg o fc k fr m s).run = some (toExec r) :=
  ⟨fun h => let ⟨n, hn⟩ := execStmt_complete h; ⟨n, hn n (Nat.le_refl n)⟩,
   fun ⟨k, hk⟩ => by cases r <;> exact execStmt_sound hk⟩

theorem callFn_iff {fr m fn args r} :
    CallFn cfg o fc fr m fn args r ↔ ∃ k, (callFn cfg o fc k fr m fn args).run = some (toFn r) :=
  ⟨fun h => let ⟨n, hn⟩ := callFn_complete h; ⟨n, hn n (Nat.le_refl n)⟩,
   fun ⟨k, hk⟩ => by cases r <;> exact callFn_sound hk⟩

/-! ## Determinism -/

theorem toRes_inj {α} {r r' : Res α} (h : toRes r = toRes r') : r = r' := by
  cases r <;> cases r' <;> simp_all [toRes]

theorem toExec_inj {r r' : ExecResult} (h : toExec r = toExec r') : r = r' := by
  cases r <;> cases r' <;> simp_all [toExec]

theorem toFn_inj {r r' : FnResult} (h : toFn r = toFn r') : r = r' := by
  cases r <;> cases r' <;> simp_all [toFn]

theorem evalExpr_det {fr m e r r'} (h : EvalExpr cfg o fc fr m e r) (h' : EvalExpr cfg o fc fr m e r') : r = r' := by
  obtain ⟨n, hn⟩ := evalExpr_complete h
  obtain ⟨n', hn'⟩ := evalExpr_complete h'
  have := (hn (n + n') (by omega)).symm.trans (hn' (n + n') (by omega))
  exact toRes_inj (Option.some.inj this)

theorem execStmt_det {fr m s r r'} (h : ExecStmt cfg o fc fr m s r) (h' : ExecStmt cfg o fc fr m s r') : r = r' := by
  obtain ⟨n, hn⟩ := execStmt_complete h
  obtain ⟨n', hn'⟩ := execStmt_complete h'
  have := (hn (n + n') (by omega)).symm.trans (hn' (n + n') (by omega))
  exact toExec_inj (Option.some.inj this)

theorem callFn_det {fr m fn args r r'} (h : CallFn cfg o fc fr m fn args r) (h' : CallFn cfg o fc fr m fn args r') :
    r = r' := by
  obtain ⟨n, hn⟩ := callFn_complete h
  obtain ⟨n', hn'⟩ := callFn_complete h'
  have := (hn (n + n') (by omega)).symm.trans (hn' (n + n') (by omega))
  exact toFn_inj (Option.some.inj this)

theorem solidityExec_det {immutables σ σ₀ g A I res conv res' conv'}
    (h : solidityExec cfg o fc immutables σ σ₀ g A I res conv)
    (h' : solidityExec cfg o fc immutables σ σ₀ g A I res' conv') : res = res' ∧ conv = conv' := by
  obtain ⟨n, hn⟩ := interpExec_complete h
  obtain ⟨n', hn'⟩ := interpExec_complete h'
  have := (hn (n + n') (by omega)).symm.trans (hn' (n + n') (by omega))
  simpa using this

theorem solidityCtorExec_det {args σ σ₀ g A I r r'}
    (h : solidityCtorExec cfg o fc args σ σ₀ g A I r)
    (h' : solidityCtorExec cfg o fc args σ σ₀ g A I r') : r = r' := by
  obtain ⟨n, hn⟩ := interpCtor_complete h
  obtain ⟨n', hn'⟩ := interpCtor_complete h'
  exact Option.some.inj ((hn (n + n') (by omega)).symm.trans (hn' (n + n') (by omega)))

end Solidity
