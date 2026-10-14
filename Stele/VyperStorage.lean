import Stele.VyperLayout
import Stele.Semantics.ValueOps

/-!
# Vyper persistent storage backend

Vyper stores bounded dynamic arrays and byte strings inline: a length word followed by
their reserved data words. Bounds are supplied by the schema-generated `VyperBounds`.
Length headers are read as raw words, mirroring the bytecode: index checks use the current
length; growth checks use the declared capacity.
As in Vyper's storage setters, clearing a dynamic value or popping an array only
changes its length; data beyond the new length can remain in storage.
-/

namespace Stele
open ABI

/-- A Vyper byte at index `i` is in the `(i / 32)`-th data word after the
length header, at the big-endian byte position within that word. -/
def vyperByteLoc (header : EVM.Word) (index : Nat) : StorageLoc :=
  { slot := header + Ethereum.UInt256.ofNat (1 + index / 32)
    offset := Fin.ofNat 32 (31 - index % 32)
    size := 1
    type := .int (.uint ⟨8, by decide⟩)
    hbound := by simp only [Fin.val_ofNat]; omega }

def vyperLeafLoc? (layout : StorageLayout) (er : EvaledStorageRef) : Option StorageLoc :=
  match layout er with
  | some (.leaf loc) => some loc
  | some (.byte header index) => some (vyperByteLoc header index)
  | _ => none

def vyperAnchor? (layout : StorageLayout) (er : EvaledStorageRef) : Option EVM.Word :=
  match layout er with
  | some (.anchor slot) => some slot
  | _ => none

/-- Read a length header as the raw word, as the bytecode does: Vyper validates lengths when it
stores them and never compares a loaded length with the declared capacity, so a corrupted header
is used as is (indexing checks it, `append` compares it with the capacity, `pop` with zero). -/
def vyperLength? (layout : StorageLayout) (bounds : VyperBounds)
    (evm : EVM.State) (er : EvaledStorageRef) : EvalResult Nat := do
  let _ ← (match bounds er with
    | some (.dynamic _) | some (.bytes _) => .ok ()
    | _ => .error .storageError : EvalResult Unit)
  let slot ← EvalResult.ofOption .storageError (vyperAnchor? layout er)
  pure (EVM.storageLoad evm evm.executionEnv.codeOwner slot).toNat

/-- Check each index in a reference before the locator can reach outside its allocation. -/
def vyperCheckSteps? (layout : StorageLayout) (bounds : VyperBounds)
    (evm : EVM.State) (base : Ident) (path : List EvaledStorageRefStep) :
    List EvaledStorageRefStep → EvalResult Unit
  | [] => .ok ()
  | step :: rest => do
      match step with
      | .aindex key =>
          let er : EvaledStorageRef := { base := base, steps := path }
          let index ← match key with
            | .int i => if i < 0 then .revert else .ok i.toNat
            | _ => .error .typeError
          match bounds er with
          | some (.fixed count) =>
              if index < count then pure () else .revert
          | some (.dynamic _) | some (.bytes _) =>
              let length ← vyperLength? layout bounds evm er
              if index < length then pure () else .revert
          | none => .error .storageError
      | _ => pure ()
      vyperCheckSteps? layout bounds evm base (path ++ [step]) rest

def vyperCheckRef? (layout : StorageLayout) (bounds : VyperBounds)
    (evm : EVM.State) (er : EvaledStorageRef) : EvalResult Unit :=
  vyperCheckSteps? layout bounds evm er.base [] er.steps

def vyperReadDataWords (evm : EVM.State) (header : EVM.Word)
    (index : Nat) : Nat → ByteArray
  | 0 => ByteArray.empty
  | n + 1 =>
      let slot := header + Ethereum.UInt256.ofNat (1 + index)
      (EVM.storageLoad evm evm.executionEnv.codeOwner slot).toByteArray ++
        vyperReadDataWords evm header (index + 1) n

def vyperWriteDataWords (evm : EVM.State) (header : EVM.Word)
    (bytes : ByteArray) (index : Nat) : Nat → EVM.State
  | 0 => evm
  | n + 1 =>
      let slot := header + Ethereum.UInt256.ofNat (1 + index)
      let word := Ethereum.uInt256OfByteArray (bytes.readWithPadding (index * 32) 32)
      let evm' := EVM.storageStore evm evm.executionEnv.codeOwner slot word
      vyperWriteDataWords evm' header bytes (index + 1) n

def vyperReadBytes? (layout : StorageLayout) (bounds : VyperBounds)
    (evm : EVM.State) (er : EvaledStorageRef) : EvalResult Value := do
  let length ← vyperLength? layout bounds evm er
  let header ← EvalResult.ofOption .storageError (vyperAnchor? layout er)
  pure (.bytes ((vyperReadDataWords evm header 0 ((length + 31) / 32)).extract 0 length))

def vyperWriteBytes? (layout : StorageLayout) (bounds : VyperBounds)
    (evm : EVM.State) (er : EvaledStorageRef) (bytes : ByteArray) : EvalResult EVM.State := do
  let capacity ← match bounds er with
    | some (.bytes n) => .ok n
    | _ => .error .storageError
  if bytes.size > capacity then .revert else do
    let _ ← vyperLength? layout bounds evm er
    let header ← EvalResult.ofOption .storageError (vyperAnchor? layout er)
    let written := vyperWriteDataWords evm header bytes 0 ((bytes.size + 31) / 32)
    pure (EVM.storageStore written written.executionEnv.codeOwner header
      (Ethereum.UInt256.ofNat bytes.size))

mutual

def vyperClearRaw? (layout : StorageLayout) (bounds : VyperBounds)
    (evm : EVM.State) (er : EvaledStorageRef) : StorageType → EvalResult EVM.State
  | .elem _ | .contract _ => do
      let loc ← EvalResult.ofOption .storageError (vyperLeafLoc? layout er)
      EvalResult.ofOption .storageError (storageLocStore evm loc (.int 0))
  | .mapping _ _ => .ok evm
  | .struct _ fields => vyperClearFields? layout bounds evm er fields
  | .tuple _ => .error .typeError
  | .array elem count =>
      match bounds er with
      | some (.fixed n) =>
          if n == count then vyperClearArray? layout bounds evm er elem count
          else .error .storageError
      | _ => .error .storageError
  | .dynamicArray _ | .bytes | .string => do
      let _ ← vyperLength? layout bounds evm er
      let slot ← EvalResult.ofOption .storageError (vyperAnchor? layout er)
      pure (EVM.storageStore evm evm.executionEnv.codeOwner slot ⟨0⟩)
  termination_by ty => (sizeOf ty, 0)

def vyperClearFields? (layout : StorageLayout) (bounds : VyperBounds)
    (evm : EVM.State) (er : EvaledStorageRef) :
    List (Ident × StorageType) → EvalResult EVM.State
  | [] => .ok evm
  | (name, ty) :: rest => do
      let evm' ← vyperClearRaw? layout bounds evm
        { er with steps := er.steps ++ [.field name] } ty
      vyperClearFields? layout bounds evm' er rest
  termination_by fields => (sizeOf fields, 0)

def vyperClearArray? (layout : StorageLayout) (bounds : VyperBounds)
    (evm : EVM.State) (er : EvaledStorageRef) (elem : StorageType) :
    Nat → EvalResult EVM.State
  | 0 => .ok evm
  | count + 1 => do
      let evm' ← vyperClearRaw? layout bounds evm
        { er with steps := er.steps ++ [.aindex (.int count)] } elem
      vyperClearArray? layout bounds evm' er elem count
  termination_by count => (sizeOf elem, count)

end

mutual

def vyperWriteRaw? (layout : StorageLayout) (bounds : VyperBounds)
    (evm : EVM.State) (er : EvaledStorageRef) : StorageType → Value → EvalResult EVM.State
  | .elem _, value
  | .contract _, value => do
      let loc ← EvalResult.ofOption .storageError (vyperLeafLoc? layout er)
      EvalResult.ofOption .storageError (storageLocStore evm loc value)
  | .struct expected fields, .struct actual values =>
      if expected == actual then vyperWriteFields? layout bounds evm er fields values
      else .error .typeError
  | .array elem count, .array values =>
      match bounds er with
      | some (.fixed n) =>
          if n != count then .error .storageError
          else if values.length == count then
            vyperWriteArray? layout bounds evm er elem 0 values
          else .error .typeError
      | _ => .error .storageError
  | .dynamicArray elem, .array values => do
      let capacity ← match bounds er with
        | some (.dynamic n) => .ok n
        | _ => .error .storageError
      if values.length > capacity then .revert else do
        let _ ← vyperLength? layout bounds evm er
        let evm' ← vyperWriteArray? layout bounds evm er elem 0 values
        let slot ← EvalResult.ofOption .storageError (vyperAnchor? layout er)
        pure (EVM.storageStore evm' evm'.executionEnv.codeOwner slot
          (Ethereum.UInt256.ofNat values.length))
  | .bytes, .bytes bytes
  | .string, .bytes bytes => vyperWriteBytes? layout bounds evm er bytes
  | _, _ => .error .typeError
  termination_by ty => (sizeOf ty, 0)

def vyperWriteFields? (layout : StorageLayout) (bounds : VyperBounds)
    (evm : EVM.State) (er : EvaledStorageRef) :
    List (Ident × StorageType) → List (Ident × Value) → EvalResult EVM.State
  | [], [] => .ok evm
  | (name, ty) :: typeRest, (actual, value) :: valueRest =>
      if name == actual then do
        let evm' ← vyperWriteRaw? layout bounds evm
          { er with steps := er.steps ++ [.field name] } ty value
        vyperWriteFields? layout bounds evm' er typeRest valueRest
      else .error .typeError
  | _, _ => .error .typeError
  termination_by types => (sizeOf types, 0)

def vyperWriteArray? (layout : StorageLayout) (bounds : VyperBounds)
    (evm : EVM.State) (er : EvaledStorageRef) (elem : StorageType) (index : Nat) :
    List Value → EvalResult EVM.State
  | [] => .ok evm
  | value :: rest => do
      let evm' ← vyperWriteRaw? layout bounds evm
        { er with steps := er.steps ++ [.aindex (.int index)] } elem value
      vyperWriteArray? layout bounds evm' er elem (index + 1) rest
  termination_by values => (sizeOf elem, sizeOf values)

end

mutual

def vyperReadRaw? (layout : StorageLayout) (bounds : VyperBounds)
    (evm : EVM.State) (er : EvaledStorageRef) : StorageType → EvalResult Value
  | .elem _ | .contract _ => do
      let loc ← EvalResult.ofOption .storageError (vyperLeafLoc? layout er)
      pure (storageLocLoad evm loc)
  | .mapping _ _ => .error .typeError
  | .struct name fields => do
      let values ← vyperReadFields? layout bounds evm er fields
      pure (.struct name values)
  | .tuple _ => .error .typeError
  | .array elem count => do
      let n ← match bounds er with
        | some (.fixed n) => .ok n
        | _ => .error .storageError
      if n != count then .error .storageError else do
        let values ← vyperReadArray? layout bounds evm er elem 0 count
        pure (.array values)
  | .dynamicArray elem => do
      let length ← vyperLength? layout bounds evm er
      let values ← vyperReadArray? layout bounds evm er elem 0 length
      pure (.array values)
  | .bytes | .string => vyperReadBytes? layout bounds evm er
  termination_by ty => (sizeOf ty, 0)

def vyperReadFields? (layout : StorageLayout) (bounds : VyperBounds)
    (evm : EVM.State) (er : EvaledStorageRef) :
    List (Ident × StorageType) → EvalResult (List (Ident × Value))
  | [] => .ok []
  | (name, ty) :: rest => do
      let value ← vyperReadRaw? layout bounds evm
        { er with steps := er.steps ++ [.field name] } ty
      let values ← vyperReadFields? layout bounds evm er rest
      pure ((name, value) :: values)
  termination_by fields => (sizeOf fields, 0)

def vyperReadArray? (layout : StorageLayout) (bounds : VyperBounds)
    (evm : EVM.State) (er : EvaledStorageRef) (elem : StorageType) (index : Nat) :
    Nat → EvalResult (List Value)
  | 0 => .ok []
  | count + 1 => do
      let value ← vyperReadRaw? layout bounds evm
        { er with steps := er.steps ++ [.aindex (.int index)] } elem
      let values ← vyperReadArray? layout bounds evm er elem (index + 1) count
      pure (value :: values)
  termination_by count => (sizeOf elem, count)

end

def vyperStorageLength? (layout : StorageLayout) (bounds : VyperBounds)
    (er : EvaledStorageRef) (ty : StorageType) (evm : EVM.State) : EvalResult Nat := do
  let _ ← vyperCheckRef? layout bounds evm er
  match ty with
  | .array _ count =>
      match bounds er with
      | some (.fixed n) => if count == n then .ok count else .error .storageError
      | _ => .error .storageError
  | .elem (.bytes width) => .ok (fixedBytesSize width)
  | .dynamicArray _ | .bytes | .string => vyperLength? layout bounds evm er
  | _ => .error .typeError

def vyperPushStorage? (layout : StorageLayout) (bounds : VyperBounds)
    (er : EvaledStorageRef) (ty : StorageType) (value : Option Value)
    (evm : EVM.State) : EvalResult EVM.State := do
  let _ ← vyperCheckRef? layout bounds evm er
  match ty, value with
  | .dynamicArray elem, some item => do
      let capacity ← match bounds er with
        | some (.dynamic n) => .ok n
        | _ => .error .storageError
      let length ← vyperLength? layout bounds evm er
      if length ≥ capacity then .revert else do
        let evm' ← vyperWriteRaw? layout bounds evm
          { er with steps := er.steps ++ [.aindex (.int length)] } elem item
        let slot ← EvalResult.ofOption .storageError (vyperAnchor? layout er)
        pure (EVM.storageStore evm' evm'.executionEnv.codeOwner slot
          (Ethereum.UInt256.ofNat (length + 1)))
  | .dynamicArray _, none => .error .typeError
  | _, _ => .error .typeError

def vyperPopStorage? (layout : StorageLayout) (bounds : VyperBounds)
    (er : EvaledStorageRef) (ty : StorageType) (evm : EVM.State) : EvalResult EVM.State := do
  let _ ← vyperCheckRef? layout bounds evm er
  match ty with
  | .dynamicArray _ => do
      let length ← vyperLength? layout bounds evm er
      if length == 0 then .revert else do
        let slot ← EvalResult.ofOption .storageError (vyperAnchor? layout er)
        pure (EVM.storageStore evm evm.executionEnv.codeOwner slot
          (Ethereum.UInt256.ofNat (length - 1)))
  | _ => .error .typeError

/-- Complete Vyper backend. The bounds function must come from the same schema as `layout`. -/
def vyperStorageBackend (layout : StorageLayout) (bounds : VyperBounds) : StorageBackend :=
  { read := fun er ty evm => do
      let _ ← vyperCheckRef? layout bounds evm er
      vyperReadRaw? layout bounds evm er ty
    write := fun er ty value evm => do
      let _ ← vyperCheckRef? layout bounds evm er
      vyperWriteRaw? layout bounds evm er ty value
    clear := fun er ty evm => do
      let _ ← vyperCheckRef? layout bounds evm er
      vyperClearRaw? layout bounds evm er ty
    length := vyperStorageLength? layout bounds
    push := vyperPushStorage? layout bounds
    pop := vyperPopStorage? layout bounds
    locate? := layout }

@[simp] theorem vyperStorageBackend_locate (layout : StorageLayout) (bounds : VyperBounds) :
    (vyperStorageBackend layout bounds).locate? = layout := rfl

end Stele
