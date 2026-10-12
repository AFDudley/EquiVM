import Solm.Storage

namespace Solm

open ABI

/-!
# Vyper storage-layout helpers

This file packages Vyper's word locations, mapping hash, and array-bound interface.
-/

def vyperWordLoc (slot : EVM.Word) (ty : ElemType) : StorageLoc :=
  { slot := slot, offset := 0, size := 32, hbound := by decide, type := ty }

def vyperUint256Loc (slot : EVM.Word) : StorageLoc :=
  vyperWordLoc slot (.int (.uint ⟨256, by decide⟩))

/-- Vyper stores `HashMap[K, V]` entries at `keccak256(baseSlot ++ key)`.

This differs from Solidity's `keccak256(key ++ baseSlot)` convention.  Nested maps compose this
function: first derive the outer map slot, then use that as the base slot for the inner map.
-/
def vyperMappingSlot (baseSlot : EVM.Word) (key : KeyValue) : EVM.Word :=
  Ethereum.uInt256OfByteArray (Ethereum.KEC (baseSlot.toByteArray ++ (keyValueToWord key).toByteArray))

/-- The kind and declared capacity of an indexed Vyper storage value. -/
inductive VyperIndexKind where
  | fixed (count : Nat)
  | dynamic (capacity : Nat)
  | bytes (capacity : Nat)
  deriving Repr, DecidableEq

/-- Bounds for array/bytes headers, generated from the same schema as the layout. -/
abbrev VyperBounds := EvaledStorageRef → Option VyperIndexKind

@[simp] theorem vyperUint256Loc_def (slot : EVM.Word) :
    vyperUint256Loc slot = vyperWordLoc slot (.int (.uint ⟨256, by decide⟩)) :=
  rfl

end Solm
