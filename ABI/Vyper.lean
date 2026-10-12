import ABI.Decode
import ABI.Signature

/-! Vyper ABI declarations retain capacities that the canonical ABI type erases. -/

namespace ABI

/-- A Vyper parameter type, including the capacities of dynamic values. -/
inductive VyperABIType where
  | elem : ElemType → VyperABIType
  | array : VyperABIType → Nat → VyperABIType
  | dynamicArray : VyperABIType → Nat → VyperABIType
  | bytes : Nat → VyperABIType
  | string : Nat → VyperABIType
  | tuple : List VyperABIType → VyperABIType
  deriving Repr, Inhabited

mutual
  /-- Erase Vyper capacities for selector calculation and the ordinary ABI decoder. -/
  def VyperABIType.toABIType : VyperABIType → ABIType
    | .elem ty => .elem ty
    | .array ty n => .array ty.toABIType n
    | .dynamicArray ty _ => .dynamicArray ty.toABIType
    | .bytes _ => .bytes
    | .string _ => .string
    | .tuple tys => .tuple (vyperABITypeList tys)

  def vyperABITypeList : List VyperABIType → List ABIType
    | [] => []
    | ty :: tys => ty.toABIType :: vyperABITypeList tys
end

mutual
  /-- Check capacities after ABI decoding, including nested arrays and tuples. -/
  def VyperABIType.withinBounds : VyperABIType → Solm.Value → Bool
    | .elem _, _ => true
    | .array elem n, .array values =>
        values.length == n && values.all elem.withinBounds
    | .dynamicArray elem capacity, .array values =>
        values.length ≤ capacity && values.all elem.withinBounds
    | .bytes capacity, .bytes bytes | .string capacity, .bytes bytes =>
        bytes.size ≤ capacity
    | .tuple tys, .tuple values => vyperABIValuesWithinBounds tys values
    | _, _ => false

  def vyperABIValuesWithinBounds : List VyperABIType → List Solm.Value → Bool
    | [], [] => true
    | ty :: tys, value :: values =>
        ty.withinBounds value && vyperABIValuesWithinBounds tys values
    | _, _ => false
end

/-- The ABI declaration of one Vyper entry point. Bounds do not change its selector. -/
structure VyperABIFunction where
  name : String
  params : List (Solm.Ident × VyperABIType)

def VyperABIFunction.names (f : VyperABIFunction) : List Solm.Ident :=
  f.params.map Prod.fst

def VyperABIFunction.types (f : VyperABIFunction) : List ABIType :=
  f.params.map (fun p => p.2.toABIType)

def VyperABIFunction.selector (f : VyperABIFunction) : ByteArray :=
  (Ethereum.KEC (String.toByteArray (printSignature ⟨f.name, f.types⟩))).extract 0 4

/-- Decode a Vyper call using its capacity-bearing declaration. The ordinary ABI decoder
handles layout and scalar checks; this layer rejects decoded values beyond Vyper capacities.
Its arguments match `ExternalCallABI.decodeCalldata?`. -/
def decodeVyperCalldata (functions : List VyperABIFunction)
    (names : List Solm.Ident) (types : List ABIType) (calldata : EVM.Bytes) :
    Option Solm.Store := do
  let f ← functions.find? (fun f => f.selector == calldata.extract 0 4)
  if f.names != names || f.types != types then none
  else do
    let store ← decodeCalldataWithMode .vyper names types calldata
    if f.params.all (fun (name, ty) =>
        match store.get? name with
        | some value => ty.withinBounds value
        | none => false) then
      some store
    else
      none

end ABI
