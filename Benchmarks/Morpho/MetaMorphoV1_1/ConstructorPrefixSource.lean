import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorInputSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorArgumentMemory

/-! Source continuations through the constructor's argument and literal allocations. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def constructorInputFrame (a : ConstructorArgs) : List UInt256 → Frame
  | [] => constructorFrame a
  | cursor :: cursors =>
    { constructorInputFrame a cursors with
      locals := (constructorInputFrame a cursors).locals.insert cursorName (uint256Value cursor) }

theorem constructorInputFrame_contract (a : ConstructorArgs) (cursors : List UInt256) :
    (constructorInputFrame a cursors).contract = contract := by
  induction cursors with
  | nil => rfl
  | cons _ _ ih => exact ih

theorem constructorInputFrame_name (a : ConstructorArgs) (cursors : List UInt256) :
    (constructorInputFrame a cursors).locals.get? "__name" = some (.bytes a.name) := by
  induction cursors with
  | nil => exact constructorFrame_name a
  | cons _ _ ih =>
    rw [constructorInputFrame, store_get_ne _ _ (by decide : (cursorName == "__name") = false)]
    exact ih

theorem constructorInputFrame_symbol (a : ConstructorArgs) (cursors : List UInt256) :
    (constructorInputFrame a cursors).locals.get? "__symbol" = some (.bytes a.symbol) := by
  induction cursors with
  | nil => exact constructorFrame_symbol a
  | cons _ _ ih =>
    rw [constructorInputFrame, store_get_ne _ _ (by decide : (cursorName == "__symbol") = false)]
    exact ih

theorem constructorInputFrame_cursor (a : ConstructorArgs) (cursor : UInt256)
    (cursors : List UInt256) (evm : State) :
    evalExpr? config (constructorInputFrame a (cursor :: cursors)) evm (.var cursorName) =
      .ok (uint256Value cursor) := by
  simp only [evalExpr?, constructorInputFrame, store_get_self, EvalResult.ofOption]

theorem constructorSourceRevertOfPrefix {σ σ₀ : AccountMap} {A : Substate}
    {I : ExecutionEnv} {g : UInt256} {frame : Frame} {rest : List Stmt} (a : ConstructorArgs)
    (hprefix : ABlock config (initState σ σ₀ (Sat256.ofUInt256 g) A I)
      (constructorFrame a) contract.ctor.body frame rest)
    (hrest : ExecBlock config frame (initState σ σ₀ (Sat256.ofUInt256 g) A I) rest .reverted) :
    steleCtorExec config contract a.values σ σ₀ g A I .reverted := by
  exact .intro rfl a.values_length (constructorLocals_bind a)
    (.execBlockRevert (hprefix.run hrest))

theorem constructorInitialAllocationPrefix (a : ConstructorArgs) (evm : State)
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hbound : 23666 + a.encoded.length < UInt256.size)
    (hfit : allocationFits ⟨480⟩ (UInt256.ofNat a.encoded.length)) :
    ABlock config evm (constructorFrame a) contract.ctor.body
      (constructorInputFrame a [UInt256.ofNat (480 + a.encoded.length)])
      (contract.ctor.body.drop 2) := by
  have hlen : evalExpr? config (constructorFrame a) evm constructorEncodedLengthExpr =
      .ok (uint256Value (UInt256.ofNat a.encoded.length)) := by
    simpa only [uint256Value, UInt256.toNat_ofNat_of_lt (show a.encoded.length < UInt256.size by omega)]
      using constructorEncodedLengthSource a evm
  have hcall := allocateCallReturns (cfg := config) (frame := constructorFrame a)
    (evm := evm) (ptr := ⟨480⟩) (size := UInt256.ofNat a.encoded.length)
    (ptrExpr := .intLit 480) (sizeExpr := constructorEncodedLengthExpr)
    cursorName allocateFunction_lookup
    (by simp only [evalExpr?, pure, uint256Value]; rfl) hlen hfit
  rw [constructorFirstCursor a hbound] at hcall
  constructor
  intro result htail
  change ExecBlock config (constructorFrame a) evm
    (.require (.binary .eq (.env .callvalue) (.intLit 0)) ::
      .internalCall allocateFunction.name [.intLit 480, constructorEncodedLengthExpr]
        cursorName :: _) result
  exact ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hv))
    (ExecBlock.consNormal hcall htail)

namespace SourceMemory

theorem constructorStringSizeSource (a : ConstructorArgs) (evm : State)
    (cursors : List UInt256) (symbol : Bool)
    (hsize : 32 + paddedSize (if symbol then a.symbol else a.name).size < UInt256.size) :
    evalExpr? config (constructorInputFrame a cursors) evm
      (.binary .add (.intLit 32)
        (constructorPaddedLengthExpr (if symbol then "__symbol" else "__name"))) =
      .ok (uint256Value (UInt256.ofNat
        (32 + paddedSize (if symbol then a.symbol else a.name).size))) := by
  rw [uint256Value, UInt256.toNat_ofNat_of_lt hsize]
  apply naturalAddSource
  · simp only [evalExpr?, pure]; rfl
  · apply constructorPaddedLengthSource
    cases symbol
    · exact constructorInputFrame_name a cursors
    · exact constructorInputFrame_symbol a cursors

theorem constructorStringCallReturns (a : ConstructorArgs) (evm : State)
    (cursor : UInt256) (cursors : List UInt256) (symbol : Bool)
    (hsize : 32 + paddedSize (if symbol then a.symbol else a.name).size < UInt256.size)
    (hfit : allocationFits cursor
      (UInt256.ofNat (32 + paddedSize (if symbol then a.symbol else a.name).size))) :
    ExecStmt config (constructorInputFrame a (cursor :: cursors)) evm
      (.internalCall allocateFunction.name
        [.var cursorName, .binary .add (.intLit 32)
          (constructorPaddedLengthExpr (if symbol then "__symbol" else "__name"))] cursorName)
      (.ok (constructorInputFrame a
        (nextCursor cursor (UInt256.ofNat (32 + paddedSize
          (if symbol then a.symbol else a.name).size)) :: cursor :: cursors)) evm) := by
  exact allocateCallReturns cursorName (by
      rw [constructorInputFrame_contract]; exact allocateFunction_lookup)
    (constructorInputFrame_cursor a cursor cursors evm)
    (constructorStringSizeSource a evm _ symbol hsize) hfit

theorem constructorStringCallReverts (a : ConstructorArgs) (evm : State)
    (cursor : UInt256) (cursors : List UInt256) (symbol : Bool)
    (hsize : 32 + paddedSize (if symbol then a.symbol else a.name).size < UInt256.size)
    (hfit : ¬ allocationFits cursor
      (UInt256.ofNat (32 + paddedSize (if symbol then a.symbol else a.name).size))) :
    ExecStmt config (constructorInputFrame a (cursor :: cursors)) evm
      (.internalCall allocateFunction.name
        [.var cursorName, .binary .add (.intLit 32)
          (constructorPaddedLengthExpr (if symbol then "__symbol" else "__name"))] cursorName)
      .reverted := by
  exact allocateCallReverts cursorName (by
      rw [constructorInputFrame_contract]; exact allocateFunction_lookup)
    (constructorInputFrame_cursor a cursor cursors evm)
    (constructorStringSizeSource a evm _ symbol hsize) hfit

theorem constructorLiteralCallReturns (a : ConstructorArgs) (evm : State)
    (cursor : UInt256) (cursors : List UInt256) (size : Nat) (hsize : size < UInt256.size)
    (hfit : allocationFits cursor (UInt256.ofNat size)) :
    ExecStmt config (constructorInputFrame a (cursor :: cursors)) evm
      (.internalCall allocateFunction.name [.var cursorName, .intLit (Int.ofNat size)] cursorName)
      (.ok (constructorInputFrame a
        (nextCursor cursor (UInt256.ofNat size) :: cursor :: cursors)) evm) := by
  exact allocateCallReturns cursorName (by
      rw [constructorInputFrame_contract]; exact allocateFunction_lookup)
    (constructorInputFrame_cursor a cursor cursors evm)
    (by simp only [evalExpr?, uint256Value, UInt256.toNat_ofNat_of_lt hsize, pure]) hfit

theorem constructorLiteralCallReverts (a : ConstructorArgs) (evm : State)
    (cursor : UInt256) (cursors : List UInt256) (size : Nat) (hsize : size < UInt256.size)
    (hfit : ¬ allocationFits cursor (UInt256.ofNat size)) :
    ExecStmt config (constructorInputFrame a (cursor :: cursors)) evm
      (.internalCall allocateFunction.name [.var cursorName, .intLit (Int.ofNat size)] cursorName)
      .reverted := by
  exact allocateCallReverts cursorName (by
      rw [constructorInputFrame_contract]; exact allocateFunction_lookup)
    (constructorInputFrame_cursor a cursor cursors evm)
    (by simp only [evalExpr?, uint256Value, UInt256.toNat_ofNat_of_lt hsize, pure]) hfit

end SourceMemory

end Benchmarks.Morpho.MetaMorphoV1_1
