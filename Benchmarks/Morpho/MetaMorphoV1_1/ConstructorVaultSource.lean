import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorSetTimelockSource
import Benchmarks.Morpho.MetaMorphoV1_1.StringStorageWrite

/-! Source assignments for the constructor's vault name and symbol. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] ConstructorArgs.encoded
set_option autoImplicit false

def constructorVaultArgName (symbol : Bool) : Ident := if symbol then "__symbol" else "__name"
def constructorVaultBytes (a : ConstructorArgs) (symbol : Bool) : ByteArray := if symbol then a.symbol else a.name
def constructorVaultAssignment (symbol : Bool) : Stmt :=
  .assign .storage ⟨stringViewField symbol, []⟩ (.var (constructorVaultArgName symbol))

theorem constructorTimelockReadyFrame_contract (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (I : ExecutionEnv) : (constructorTimelockReadyFrame a ok out I).contract = contract := by
  have ho : (constructorOwnershipFrame (constructorDomainReadyFrame a ok out I)).contract = contract :=
    constructorDomainReadyFrame_contract a ok out I
  have ht := constructorTimelockCheckedFrame_contract
    (frame := constructorOwnershipFrame (constructorDomainReadyFrame a ok out I)) a.initialTimelock ho
  simpa only [constructorTimelockReadyFrame, constructorSetTimelockFrame] using ht

theorem constructorTimelockReadyFrame_preserves (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (I : ExecutionEnv) (name : Ident) (hc : (cursorName == name) = false)
    (hs : (slotsAndCursorName == name) = false) (hd : ("decimalResult" == name) = false)
    (hh : ("domain" == name) = false) (ho : ("initOwner" == name) = false)
    (ht : ("checkTime" == name) = false) (hi : ("initTime" == name) = false) :
    (constructorTimelockReadyFrame a ok out I).locals.get? name =
      (constructorFrame a).locals.get? name := by
  rw [constructorTimelockReadyFrame, constructorSetTimelockFrame, store_get_ne _ _ hi]
  unfold constructorTimelockCheckedFrame
  split
  · rw [constructorOwnershipFrame, store_get_ne _ _ ho]
    exact constructorDomainReadyFrame_preserves a ok out I name hc hs hd hh
  · rw [store_get_ne _ _ ht, constructorOwnershipFrame, store_get_ne _ _ ho]
    exact constructorDomainReadyFrame_preserves a ok out I name hc hs hd hh

theorem constructorTimelockReadyFrame_string (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (I : ExecutionEnv) (symbol : Bool) :
    (constructorTimelockReadyFrame a ok out I).locals.get? (constructorVaultArgName symbol) =
      some (.bytes (constructorVaultBytes a symbol)) := by
  rw [constructorTimelockReadyFrame_preserves a ok out I _
    (by cases symbol <;> decide) (by cases symbol <;> decide) (by cases symbol <;> decide)
    (by cases symbol <;> decide) (by cases symbol <;> decide) (by cases symbol <;> decide)
    (by cases symbol <;> decide)]
  cases symbol with
  | false => exact constructorFrame_name a
  | true => exact constructorFrame_symbol a

theorem constructorTimelockReadyFrame_unshadowed (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (I : ExecutionEnv) (symbol : Bool) :
    (constructorTimelockReadyFrame a ok out I).locals.get? (stringViewField symbol) = none := by
  rw [constructorTimelockReadyFrame_preserves a ok out I _
    (by cases symbol <;> decide) (by cases symbol <;> decide) (by cases symbol <;> decide)
    (by cases symbol <;> decide) (by cases symbol <;> decide) (by cases symbol <;> decide)
    (by cases symbol <;> decide)]
  cases symbol <;> simp [constructorFrame, constructorLocals, stringViewField]

theorem constructorVaultAssign {frame : Frame} {evm : State} {bytes : ByteArray} (symbol : Bool)
    (hcontract : frame.contract = contract)
    (hget : frame.locals.get? (constructorVaultArgName symbol) = some (.bytes bytes))
    (hbase : frame.locals.get? (stringViewField symbol) = none)
    (hvalid : storageStringValid (storageStringHeader evm (stringViewSlot symbol))) :
    ExecStmt config frame evm (constructorVaultAssignment symbol)
      (.ok frame (storageStringWriteState evm (stringViewSlot symbol) bytes)) := by
  rcases frame with ⟨decl, locals, imms⟩
  change decl = contract at hcontract
  subst decl
  apply ExecStmt.assign (value := .bytes bytes)
    (by simp only [evalExpr?, hget, EvalResult.ofOption])
  exact assignStorageString symbol evm locals imms bytes hbase hvalid

theorem constructorVaultAssignRevert {frame : Frame} {evm : State} {bytes : ByteArray} (symbol : Bool)
    (hcontract : frame.contract = contract)
    (hget : frame.locals.get? (constructorVaultArgName symbol) = some (.bytes bytes))
    (hbase : frame.locals.get? (stringViewField symbol) = none)
    (hbad : ¬ storageStringValid (storageStringHeader evm (stringViewSlot symbol))) :
    ExecStmt config frame evm (constructorVaultAssignment symbol) .reverted := by
  rcases frame with ⟨decl, locals, imms⟩
  change decl = contract at hcontract
  subst decl
  apply ExecStmt.assignStoreRevert (value := .bytes bytes)
    (by simp only [evalExpr?, hget, EvalResult.ofOption])
  exact assignStorageStringReverts symbol evm locals imms bytes hbase hbad

theorem constructorVaultAssignBodySplit (symbol : Bool) :
    contract.ctor.body.drop (if symbol then 31 else 29) =
      constructorVaultAssignment symbol :: contract.ctor.body.drop (if symbol then 32 else 30) := by
  cases symbol <;> rfl

end Benchmarks.Morpho.MetaMorphoV1_1
