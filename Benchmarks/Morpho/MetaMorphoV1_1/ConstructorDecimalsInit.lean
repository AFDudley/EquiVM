import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDecimalsRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDecimalsFunction
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorLiteralSource
import Benchmarks.Morpho.MetaMorphoV1_1.CursorCallSource

/-! Couple the constructor's first external query and continue with its decimals result. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def constructorDecimalsCursor (a : ConstructorArgs) (out : ByteArray) : UInt256 :=
  callReturnCursor (nextCursor (UInt256.ofNat (a.stringsEnd + 160)) ⟨36⟩) out

def constructorDecimalsReadyFrame (a : ConstructorArgs) (ok : Bool) (out : ByteArray) : Frame :=
  cursorResultFrame (constructorReadyFrame a) "decimalResult" (constructorDecimalsValue ok out)
    (constructorDecimalsCursor a out)

theorem constructorInputFrame_asset (a : ConstructorArgs) (cursors : List UInt256) :
    (constructorInputFrame a cursors).locals.get? "assetAddress" = some (.address a.asset) := by
  induction cursors with
  | nil =>
    apply Std.HashMap.getElem?_ofList_of_mem (k := "assetAddress") (by decide)
    · simp
    · simp
  | cons _ _ ih =>
    rw [constructorInputFrame, store_get_ne _ _ (by decide : (cursorName == "assetAddress") = false)]
    exact ih

theorem constructorDecimalsArgs (a : ConstructorArgs) (evm : State) :
    evalExprs? config (constructorReadyFrame a) evm [.var "assetAddress", .var cursorName] =
      .ok [.address a.asset, uint256Value (UInt256.ofNat (a.stringsEnd + 160))] := by
  have ha : evalExpr? config (constructorReadyFrame a) evm (.var "assetAddress") =
      .ok (.address a.asset) := by
    simp only [evalExpr?, constructorReadyFrame, constructorInputFrame_asset, EvalResult.ofOption]
  have hp : evalExpr? config (constructorReadyFrame a) evm (.var cursorName) =
      .ok (uint256Value (UInt256.ofNat (a.stringsEnd + 160))) :=
    constructorInputFrame_cursor a _ _ evm
  simp only [evalExprs?, ha, hp, bind, EvalResult.bind, pure]

theorem constructorDecimalsCallerPrefix {frame : Frame} {evm evm' : State}
    {asset : AccountAddress} {ptr : UInt256} {ok : Bool} {out : ByteArray}
    {tail : List Stmt} {result : ExecResult}
    (hcontract : frame.contract = contract)
    (hargs : evalExprs? config frame evm [.var "assetAddress", .var cursorName] =
      .ok [.address asset, uint256Value ptr])
    (hfit : allocationFits ptr ⟨36⟩)
    (hcall : typedCallViaEVM config evm asset "decimals" 0 [] (ok, evm', out) false)
    (hreturn : callReturnFits (nextCursor ptr ⟨36⟩) out)
    (htail : ExecBlock config (cursorResultFrame frame "decimalResult" (constructorDecimalsValue ok out)
      (callReturnCursor (nextCursor ptr ⟨36⟩) out)) evm' tail result) :
    ExecBlock config frame evm (constructorDecimalsCall ++ tail) result := by
  rcases frame with ⟨decl, locals, imms⟩
  change decl = contract at hcontract
  subst decl
  have hsource := constructorDecimalsStatementReturns locals imms asset ptr ok out
    [.var "assetAddress", .var cursorName] slotsAndCursorName hargs hfit hcall hreturn
  exact cursorCallPrefix (by decide) hsource htail

set_option maxRecDepth 2000 in
theorem constructorDecimalsInit {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (hs : SourceState s0 I σ evm)
    (hptr : a.stringsEnd + 160 < 2 ^ 64) (hmem : 128 ≤ mem.size)
    (hzero : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hfree : memLoad ⟨64⟩ mem = UInt256.ofNat (a.stringsEnd + 160))
    (rd : RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨434⟩
      (constructorMetadataTail a a.stringsEnd true) mem aw rdata σ k C) :
    (ExecBlock config (constructorReadyFrame a) evm (contract.ctor.body.drop 10) .reverted ∧
      RDrev (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) g s0) ∨
    (∃ (evm' : State) (ok : Bool) (out : ByteArray) (aw' : UInt256) (k' C' : Nat),
      (∀ result, ExecBlock config (constructorDecimalsReadyFrame a ok out) evm'
          (contract.ctor.body.drop 13) result →
        ExecBlock config (constructorReadyFrame a) evm (contract.ctor.body.drop 10) result) ∧
      SourceState s0 I evm'.accountMap evm' ∧
      (constructorDecimalsCursor a out).toNat < 2 ^ 64 ∧
      a.stringsEnd + 160 ≤ (constructorDecimalsCursor a out).toNat ∧
      ByteMemoryPrefix mem
        (constructorDecimalsMemory mem (UInt256.ofNat (a.stringsEnd + 160)) out)
        (a.stringsEnd + 160) ∧
      memLoad ⟨64⟩ (constructorDecimalsMemory mem (UInt256.ofNat (a.stringsEnd + 160)) out) =
        constructorDecimalsCursor a out ∧
      RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨443⟩
        (constructorDecimalsWord ok out :: (if constructorDecimalsValid ok out then ⟨1⟩ else ⟨0⟩) ::
          constructorMetadataTail a a.stringsEnd true)
        (constructorDecimalsMemory mem (UInt256.ofNat (a.stringsEnd + 160)) out)
        aw' out evm'.accountMap k' C') := by
  have hp : (UInt256.ofNat (a.stringsEnd + 160)).toNat = a.stringsEnd + 160 :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2 ^ 256; omega)
  obtain ⟨_, _, _, r1⟩ := constructorDecimalsEntry a a.stringsEnd rd
  rcases constructorDecimalsRuntime a.asset (by simp [constructorMetadataTail])
    (by rw [hp]; omega) (by rwa [hp]) hmem hzero hfree hs (by native_decide) r1 with
      hfail | ⟨hfit, evm', ok, out, hc, hs', hrest⟩
  · exact .inl ⟨ExecBlock.consRevert (constructorDecimalsStatementRequestReverts evm _ _ a.asset _ _ _
      (constructorDecimalsArgs a evm) hfail.1), hfail.2⟩
  rcases hrest with hfail | ⟨hreturn, aw2, k2, C2, r2⟩
  · exact .inl ⟨ExecBlock.consRevert (constructorDecimalsStatementReturnReverts _ _ a.asset _ ok out _ _
      (constructorDecimalsArgs a evm) hfit hc hfail.1), hfail.2⟩
  have hb := callReturnCursor_bound _ out hfit.1 hreturn
  have hstart := hfit.2
  rw [hp] at hstart
  refine .inr ⟨evm', ok, out, aw2, k2, C2, ?_, hs', hb.1, le_trans hstart hb.2, ?_,
    constructorDecimalsMemory_free mem _ out (by rw [hp]; omega) hfit, r2⟩
  · intro result htail
    change ExecBlock config (constructorReadyFrame a) evm
      (constructorDecimalsCall ++ contract.ctor.body.drop 13) result
    exact constructorDecimalsCallerPrefix (constructorInputFrame_contract a _)
      (constructorDecimalsArgs a evm) hfit hc hreturn htail
  · simpa only [hp] using constructorDecimalsMemory_prefix mem _ out hfit

end Benchmarks.Morpho.MetaMorphoV1_1
