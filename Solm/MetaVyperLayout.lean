import Lean
import Solm.VyperStorage

/-!
# Compile-time Vyper storage layout

`vyperLayout! [decls]` accepts ordinary Solm storage declarations when every type has
a statically known size. `vyperBoundedLayout! [decls]` accepts Vyper declarations with
the capacity of each dynamic array, byte string, and string recorded in its type.
Both macros emit a closed locator rather than traversing the schema at runtime.
`vyperStorage!` and `vyperBoundedStorage!` generate the matching bound lookup and
construct a Vyper backend from the two functions.

Capacities determine reserved slots. The backend checks runtime indices and growth.
Byte locations remain symbolic as `StorageAddr.byte`, interpreted by `vyperStorageBackend`
using Vyper's inline length and data words.
-/

namespace Solm
open ABI Lean Elab Term Meta

/-- The extra capacity information needed to allocate Vyper's inline dynamic values. -/
inductive VyperStorageType where
  | elem : ElemType → VyperStorageType
  | contract : Ident → VyperStorageType
  | mapping : ElemType → VyperStorageType → VyperStorageType
  | struct : Ident → List (Ident × VyperStorageType) → VyperStorageType
  | array : VyperStorageType → Nat → VyperStorageType
  | dynamicArray : VyperStorageType → Nat → VyperStorageType
  | bytes : Nat → VyperStorageType
  | string : Nat → VyperStorageType
  deriving Repr, Inhabited

structure VyperStorageDecl where
  name : Ident
  ty : VyperStorageType
  deriving Repr, Inhabited

namespace MetaVyperLayout

mutual
private partial def fromStorageType? : StorageType → Option VyperStorageType
  | .elem ty => some (.elem ty)
  | .contract name => some (.contract name)
  | .mapping key value => .mapping key <$> fromStorageType? value
  | .struct name fields => .struct name <$> fromFields? fields
  | .array elem count => return .array (← fromStorageType? elem) count
  | .dynamicArray _ | .bytes | .string | .tuple _ => none

private partial def fromFields? : List (Ident × StorageType) →
    Option (List (Ident × VyperStorageType))
  | [] => some []
  | (name, ty) :: rest => return (name, ← fromStorageType? ty) :: (← fromFields? rest)
end

private def fromDecls? (decls : List StorageDecl) : Option (List VyperStorageDecl) :=
  decls.mapM fun decl => do
    return { name := decl.name, ty := (← fromStorageType? decl.ty) }

private def supportedKey : ElemType → Bool
  | .bool | .address | .int _ | .bytes _ => true
  | .fixed _ | .function => false

mutual
private partial def words? : VyperStorageType → Option Nat
  | .elem (.fixed _) | .elem .function => none
  | .elem _ | .contract _ | .mapping _ _ => some 1
  | .struct _ fields => fieldWords? fields
  | .array elem count =>
      if count == 0 then none else return count * (← words? elem)
  | .dynamicArray elem capacity =>
      if capacity == 0 then none else return 1 + capacity * (← words? elem)
  | .bytes capacity | .string capacity =>
      if capacity == 0 then none else some (1 + (capacity + 31) / 32)

private partial def fieldWords? : List (Ident × VyperStorageType) → Option Nat
  | [] => some 0
  | (_, ty) :: rest => return (← words? ty) + (← fieldWords? rest)
end

private inductive StepPattern where
  | field : Ident → StepPattern
  | mindex : Name → StepPattern
  | aindex : Name → StepPattern

private structure Case where
  steps : List StepPattern
  body : Term

private def num (n : Nat) : Term := Syntax.mkNumLit (toString n)
private def str (s : String) : Term := Syntax.mkStrLit s

private def plus (slot : Term) (n : Nat) : TermElabM Term :=
  if n == 0 then pure slot
  else `(term| $slot + Ethereum.UInt256.ofNat $(num n))

private def elemTerm : ElemType → TermElabM Term
  | .bool => `(term| ABI.ElemType.bool)
  | .address => `(term| ABI.ElemType.address)
  | .int (.uint w) => `(term| ABI.ElemType.int (.uint ⟨$(num w.val), by decide⟩))
  | .int (.sint w) => `(term| ABI.ElemType.int (.sint ⟨$(num w.val), by decide⟩))
  | .bytes w => `(term| ABI.ElemType.bytes ⟨$(num w.val), by decide⟩)
  | .fixed _ | .function => throwError "unsupported Vyper elementary storage type"

private def leaf (slot : Term) (elem : ElemType) : TermElabM Term := do
  let ty ← elemTerm elem
  `(term| some (StorageAddr.leaf (vyperWordLoc $slot $ty)))

private def bindCases (cases : List Case) (name : Name) (value : Term) :
    TermElabM (List Case) :=
  cases.mapM fun c => do
    let ident := mkIdent name
    pure { c with body := (← `(term| let $ident:ident := $value; $(c.body))) }

private partial def cases (ty : VyperStorageType) (slot : Term)
    (path : List StepPattern) : TermElabM (List Case) := do
  match ty with
  | .elem elem => return [{ steps := path, body := (← leaf slot elem) }]
  | .contract _ => return [{ steps := path, body := (← leaf slot .address) }]
  | .mapping key value =>
      unless supportedKey key do throwError "unsupported Vyper mapping key type"
      let keyName ← mkFreshUserName `key
      let mappedName ← mkFreshUserName `mapped
      let keyTerm := mkIdent keyName
      let mappedTerm := mkIdent mappedName
      let valueTerm ← `(term| vyperMappingSlot $slot $keyTerm)
      bindCases (← cases value mappedTerm (path ++ [.mindex keyName])) mappedName valueTerm
  | .array elem _ | .dynamicArray elem _ =>
      let some stride := words? elem
        | throwError "unsupported Vyper array element type"
      if stride == 0 then throwError "zero-sized Vyper array element"
      let base ← match ty with
        | .dynamicArray _ _ => plus slot 1
        | _ => pure slot
      let indexName ← mkFreshUserName `index
      let elementName ← mkFreshUserName `element
      let index := mkIdent indexName
      let element := mkIdent elementName
      let value ← `(term| $base + Ethereum.UInt256.ofNat
        ((keyValueToWord $index).toNat * $(num stride)))
      let indexed ← bindCases (← cases elem element (path ++ [.aindex indexName]))
        elementName value
      match ty with
      | .dynamicArray _ _ =>
          return { steps := path, body := (← `(term| some (StorageAddr.anchor $slot))) } :: indexed
      | _ => return indexed
  | .bytes _ | .string _ =>
      -- `StorageAddr.byte` is symbolic. A Vyper backend must interpret its header
      -- as a length word followed by in-place data, not Solidity's short/long encoding.
      let indexName ← mkFreshUserName `index
      let index := mkIdent indexName
      let byteBody ← `(term| some (StorageAddr.byte $slot (keyValueToWord $index).toNat))
      return [
        { steps := path, body := (← `(term| some (StorageAddr.anchor $slot))) },
        { steps := path ++ [.aindex indexName], body := byteBody } ]
  | .struct _ fields =>
      let mut offset := 0
      let mut out := []
      for (name, fieldTy) in fields do
        let some size := words? fieldTy
          | throwError "unsupported Vyper struct field type"
        let fieldSlot ← plus slot offset
        out := out ++ (← cases fieldTy fieldSlot (path ++ [.field name]))
        offset := offset + size
      return out

private def stepTerm : StepPattern → TermElabM Term
  | .field name => `(term| .field $(str name))
  | .mindex name => `(term| .mindex $(mkIdent name))
  | .aindex name => `(term| .aindex $(mkIdent name))

private def stepsTerm : List StepPattern → TermElabM Term
  | [] => `(term| [])
  | head :: tail => do
      let h ← stepTerm head
      let t ← stepsTerm tail
      `(term| $h :: $t)

private def generate (decls : List VyperStorageDecl) : TermElabM Term := do
  let names := decls.map (·.name)
  unless names.eraseDups.length == names.length do
    throwError "duplicate Vyper storage declaration name"
  let refName ← mkFreshUserName `ref
  let ref := mkIdent refName
  let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  let mut offset := 0
  for decl in decls do
    let some size := words? decl.ty
      | throwError "unsupported Vyper storage type"
    let base ← `(term| (Ethereum.UInt256.ofNat $(num offset)))
    for c in (← cases decl.ty base []) do
      let name := str decl.name
      let steps ← stepsTerm c.steps
      let body := c.body
      alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $name, $steps => $body))
    offset := offset + size
  alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | _, _ => none))
  let body ← `(term| match ($ref).base, ($ref).steps with $alts:matchAlt*)
  `(term| ((fun $ref:ident => $body) : StorageLayout))

private partial def boundCases (ty : VyperStorageType)
    (path : List StepPattern) : TermElabM (List Case) := do
  match ty with
  | .elem _ | .contract _ => return []
  | .mapping _ value =>
      let indexName ← mkFreshUserName `key
      boundCases value (path ++ [.mindex indexName])
  | .struct _ fields =>
      let mut out := []
      for (name, fieldTy) in fields do
        out := out ++ (← boundCases fieldTy (path ++ [.field name]))
      return out
  | .array elem count =>
      let indexName ← mkFreshUserName `index
      let rest ← boundCases elem (path ++ [.aindex indexName])
      return { steps := path, body := (← `(term| some (VyperIndexKind.fixed $(num count)))) } :: rest
  | .dynamicArray elem capacity =>
      let indexName ← mkFreshUserName `index
      let rest ← boundCases elem (path ++ [.aindex indexName])
      return { steps := path, body := (← `(term| some (VyperIndexKind.dynamic $(num capacity)))) } :: rest
  | .bytes capacity | .string capacity =>
      return [{ steps := path, body := (← `(term| some (VyperIndexKind.bytes $(num capacity)))) }]

private def generateBounds (decls : List VyperStorageDecl) : TermElabM Term := do
  let refName ← mkFreshUserName `ref
  let ref := mkIdent refName
  let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  for decl in decls do
    for c in (← boundCases decl.ty []) do
      let name := str decl.name
      let steps ← stepsTerm c.steps
      let body := c.body
      alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | $name, $steps => $body))
  alts := alts.push (← `(Lean.Parser.Term.matchAltExpr| | _, _ => none))
  let body ← `(term| match ($ref).base, ($ref).steps with $alts:matchAlt*)
  `(term| ((fun $ref:ident => $body) : VyperBounds))

private unsafe def evalClosed (alpha : Type) (typeStx valueStx : Term) : TermElabM alpha := do
  let type ← elabType typeStx
  let value ← elabTermEnsuringType valueStx type
  evalExpr alpha type value

private def elaboratePlain (declsStx : Term) : TermElabM Term := do
  let decls ← unsafe evalClosed (List StorageDecl) (← `(term| List StorageDecl)) declsStx
  let some converted := fromDecls? decls
    | throwError "Vyper dynamic arrays, bytes, and strings require vyperBoundedLayout! with explicit capacities"
  generate converted

private def elaborateBounded (declsStx : Term) : TermElabM Term := do
  let decls ← unsafe evalClosed (List VyperStorageDecl)
    (← `(term| List VyperStorageDecl)) declsStx
  generate decls

private def elaboratePlainBounds (declsStx : Term) : TermElabM Term := do
  let decls ← unsafe evalClosed (List StorageDecl) (← `(term| List StorageDecl)) declsStx
  let some converted := fromDecls? decls
    | throwError "Vyper dynamic arrays, bytes, and strings require vyperBoundedBounds! with explicit capacities"
  let _ ← generate converted
  generateBounds converted

private def elaborateBoundedBounds (declsStx : Term) : TermElabM Term := do
  let decls ← unsafe evalClosed (List VyperStorageDecl)
    (← `(term| List VyperStorageDecl)) declsStx
  let _ ← generate decls
  generateBounds decls

elab "vyperLayout! " "[" decls:term "]" : term => do
  elabTerm (← elaboratePlain decls) none

elab "vyperBoundedLayout! " "[" decls:term "]" : term => do
  elabTerm (← elaborateBounded decls) none

elab "vyperBounds! " "[" decls:term "]" : term => do
  elabTerm (← elaboratePlainBounds decls) none

elab "vyperBoundedBounds! " "[" decls:term "]" : term => do
  elabTerm (← elaborateBoundedBounds decls) none

macro "vyperStorage! " "[" decls:term "]" : term =>
  `(vyperStorageBackend (vyperLayout! [$decls]) (vyperBounds! [$decls]))

macro "vyperBoundedStorage! " "[" decls:term "]" : term =>
  `(vyperStorageBackend (vyperBoundedLayout! [$decls])
    (vyperBoundedBounds! [$decls]))

end MetaVyperLayout
end Solm
