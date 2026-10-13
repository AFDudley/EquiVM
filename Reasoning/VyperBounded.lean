import Reasoning.VyperDispatch

/-!
# Vyper's bounded storage backend

Proof support for `vyperBoundedStorage!`: full-word leaves, the length header of a bounded
`DynArray`, its index checks, `push`/`pop`, and the `arrayLength` expression.  The lemmas take the
layout facts (`layout er = some (.anchor s)`, `bounds er = some (.dynamic cap)`) as hypotheses;
the schema-generated locator discharges them by `rfl`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch

namespace Reasoning.VyperBounded

/-! ## Full-word leaves -/

/-- Any scalar value with a word stores that word in a full-word leaf. -/
theorem storageLocStore_vyperWord_value (evm : EVM.State) (slot : UInt256) (ty : ElemType)
    (v : Value) (w : UInt256) (hw : valueToWord v = some w) :
    storageLocStore evm (vyperWordLoc slot ty) v =
      some (Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot w) := by
  unfold storageLocStore storageLocWriteWord vyperWordLoc
  simp only [hw, bind, Option.bind]
  have hslen := (EVM.Word.toBytesLEWithSizeProof
    (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)).2
  have hvlen := (EVM.Word.toBytesLEWithSizeProof w).2
  congr 2
  apply u256_inj
  show fromBytes'
      (List.take (0 : Fin 32).val _ ++ List.take (32 : Fin 33).val _
        ++ List.drop ((0 : Fin 32).val + (32 : Fin 33).val) _) = w.toNat
  rw [show (0 : Fin 32).val = 0 from rfl, show (32 : Fin 33).val = 32 from rfl,
    List.take_zero, List.nil_append, List.drop_eq_nil_of_le (by rw [hslen]),
    List.append_nil, List.take_of_length_le (by rw [hvlen]), fromBytes'_toBytesLEWithSizeProof]

theorem storageLocStore_vyperWord_address (evm : EVM.State) (slot : UInt256) (a : AccountAddress) :
    storageLocStore evm (vyperWordLoc slot .address) (.address a) =
      some (Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot (UInt256.ofNat a.val)) :=
  storageLocStore_vyperWord_value evm slot .address (.address a) _ rfl

/-- A full-word leaf write through the raw writer. -/
theorem vyperWriteRaw_elem {layout : StorageLayout} {bounds : VyperBounds} {evm evm' : EVM.State}
    {er : EvaledStorageRef} {t : ElemType} {loc : StorageLoc} {v : Value}
    (hloc : layout er = some (.leaf loc)) (hstore : storageLocStore evm loc v = some evm') :
    vyperWriteRaw? layout bounds evm er (.elem t) v = .ok evm' := by
  simp [vyperWriteRaw?, vyperLeafLoc?, hloc, hstore, EvalResult.ofOption, bind, EvalResult.bind]

/-- A full-word leaf read through the raw reader. -/
theorem vyperReadRaw_elem {layout : StorageLayout} {bounds : VyperBounds} {evm : EVM.State}
    {er : EvaledStorageRef} {t : ElemType} {loc : StorageLoc}
    (hloc : layout er = some (.leaf loc)) :
    vyperReadRaw? layout bounds evm er (.elem t) = .ok (storageLocLoad evm loc) := by
  simp [vyperReadRaw?, vyperLeafLoc?, hloc, EvalResult.ofOption, bind, EvalResult.bind, pure]

/-! ## Length headers -/

/-- The length of a bounded array is its raw header word. -/
theorem vyperLength_ok {layout : StorageLayout} {bounds : VyperBounds} {evm : EVM.State}
    {er : EvaledStorageRef} {cap : Nat} {s : UInt256}
    (hbounds : bounds er = some (.dynamic cap)) (hanchor : layout er = some (.anchor s)) :
    vyperLength? layout bounds evm er =
      .ok (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner s).toNat := by
  simp [vyperLength?, hbounds, vyperAnchor?, hanchor, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem vyperStorageLength_dynamic {layout : StorageLayout} {bounds : VyperBounds} {evm : EVM.State}
    {er : EvaledStorageRef} {elem : StorageType} {cap : Nat} {s : UInt256}
    (hcheck : vyperCheckRef? layout bounds evm er = .ok ())
    (hbounds : bounds er = some (.dynamic cap)) (hanchor : layout er = some (.anchor s)) :
    vyperStorageLength? layout bounds er (.dynamicArray elem) evm =
      .ok (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner s).toNat := by
  simp [vyperStorageLength?, hcheck, vyperLength_ok hbounds hanchor, bind, EvalResult.bind]

/-- `arr.length` of a bounded array through the Vyper backend. -/
theorem evalExpr_arrayLength_vyper {cfg : Config} {layout : StorageLayout} {bounds : VyperBounds}
    {stele : Frame} {evm : EVM.State} {slot : StorageRef} {er : EvaledStorageRef}
    {elem : StorageType} {cap : Nat} {s : UInt256}
    (hbase : stele.locals.get? slot.base = none)
    (her : evalStorageRef cfg stele evm slot = .ok er)
    (hty : storageTypeAt? stele.contract.storage er = some (.dynamicArray elem))
    (hbackend : cfg.storageBackend = vyperStorageBackend layout bounds)
    (hcheck : vyperCheckRef? layout bounds evm er = .ok ())
    (hbounds : bounds er = some (.dynamic cap)) (hanchor : layout er = some (.anchor s)) :
    evalExpr? cfg stele evm (.arrayLength .storage slot) =
      .ok (.int (Int.ofNat (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner s).toNat)) := by
  rw [evalExpr?]
  simp only [resolveStorageRef?_ok hbase her hty, bind, EvalResult.bind, hbackend, vyperStorageBackend,
    vyperStorageLength_dynamic hcheck hbounds hanchor]
  rfl

/-! ## Index checks -/

/-- The reference check of `arr[i]` for an index below the current length. -/
theorem vyperCheckRef_aindex_ok {layout : StorageLayout} {bounds : VyperBounds} {evm : EVM.State}
    {base : Ident} {i cap : Nat} {s : UInt256}
    (hbounds : bounds { base := base, steps := [] } = some (.dynamic cap))
    (hanchor : layout { base := base, steps := [] } = some (.anchor s))
    (hlt : i < (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner s).toNat) :
    vyperCheckRef? layout bounds evm { base := base, steps := [.aindex (.int (Int.ofNat i))] } = .ok () := by
  simp [vyperCheckRef?, vyperCheckSteps?, hbounds, vyperLength_ok hbounds hanchor, hlt,
    bind, EvalResult.bind, pure]

/-- Evaluating `arr[e]` with the index below the length. -/
theorem evalStorageRef_aindex_ok {cfg : Config} {stele : Frame} {evm : EVM.State}
    {base : Ident} {idx : Expr} {i len : Nat} {ty : StorageType}
    (hidx : evalExpr? cfg stele evm idx = .ok (.int (Int.ofNat i)))
    (hty : storageTypeAt? stele.contract.storage { base := base, steps := [] } = some ty)
    (hdyn : ∃ elem, ty = .dynamicArray elem)
    (hlen : cfg.storageBackend.length { base := base, steps := [] } ty evm = .ok len)
    (hlt : i < len) :
    evalStorageRef cfg stele evm { base := base, steps := [.aindex idx] } =
      .ok { base := base, steps := [.aindex (.int (Int.ofNat i))] } := by
  obtain ⟨elem, rfl⟩ := hdyn
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, hidx, valueToKey?,
    arrayIndexInBounds?, hty, hlen, hlt, bind, EvalResult.bind, pure, EvalResult.ofOption]

/-- Evaluating `arr[e]` with the index at or beyond the length reverts. -/
theorem evalStorageRef_aindex_revert {cfg : Config} {stele : Frame} {evm : EVM.State}
    {base : Ident} {idx : Expr} {i len : Nat} {ty : StorageType}
    (hidx : evalExpr? cfg stele evm idx = .ok (.int (Int.ofNat i)))
    (hty : storageTypeAt? stele.contract.storage { base := base, steps := [] } = some ty)
    (hdyn : ∃ elem, ty = .dynamicArray elem)
    (hlen : cfg.storageBackend.length { base := base, steps := [] } ty evm = .ok len)
    (hge : len ≤ i) :
    evalStorageRef cfg stele evm { base := base, steps := [.aindex idx] } = .revert := by
  obtain ⟨elem, rfl⟩ := hdyn
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, hidx, valueToKey?,
    arrayIndexInBounds?, hty, hlen, bind, EvalResult.bind, pure, EvalResult.ofOption,
    show ¬ (i < len) from by omega]

/-- A reverting storage reference reverts the storage read. -/
theorem evalExpr_storage_revert {cfg : Config} {stele : Frame} {evm : EVM.State} {slot : StorageRef}
    (hbase : stele.locals.get? slot.base = none)
    (her : evalStorageRef cfg stele evm slot = .revert) :
    evalExpr? cfg stele evm (.storage slot) = .revert := by
  rw [evalExpr?, Std.HashMap.get?_eq_getElem?] at *
  simp [resolveStorageRef?, hbase, her, bind, EvalResult.bind]

/-! ## `push` and `pop` -/

/-- `arr.push(v)` with room: the element is written at the old length, then the length grows. -/
theorem pushArray_vyper_ok {cfg : Config} {layout : StorageLayout} {bounds : VyperBounds}
    {stele : Frame} {evm evm1 : EVM.State} {slot : StorageRef} {er : EvaledStorageRef}
    {elem : StorageType} {cap : Nat} {s : UInt256} {v : Value}
    (hbase : stele.locals.get? slot.base = none)
    (her : evalStorageRef cfg stele evm slot = .ok er)
    (hty : storageTypeAt? stele.contract.storage er = some (.dynamicArray elem))
    (hbackend : cfg.storageBackend = vyperStorageBackend layout bounds)
    (hcheck : vyperCheckRef? layout bounds evm er = .ok ())
    (hbounds : bounds er = some (.dynamic cap)) (hanchor : layout er = some (.anchor s))
    (hcap : (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner s).toNat < cap)
    (hwrite : vyperWriteRaw? layout bounds evm
      { er with steps := er.steps ++ [.aindex (.int (Int.ofNat
        (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner s).toNat))] } elem v = .ok evm1)
    (hnotrans : usesTransientStorage stele slot = false) :
    pushArray? cfg stele evm slot (some v) =
      .ok (Stele.EVM.storageStore evm1 evm1.executionEnv.codeOwner s
        (UInt256.ofNat ((Stele.EVM.storageLoad evm evm.executionEnv.codeOwner s).toNat + 1))) := by
  simp only [pushArray?, hnotrans, Bool.false_eq_true, if_false, resolveStorageRef?_ok hbase her hty,
    bind, EvalResult.bind, hbackend, vyperStorageBackend, vyperPushStorage?, hcheck,
    vyperLength_ok hbounds hanchor, hbounds, pure]
  have hwrite' := hwrite
  simp only [Int.ofNat_eq_natCast] at hwrite'
  simp [show ¬ ((Stele.EVM.storageLoad evm evm.executionEnv.codeOwner s).toNat ≥ cap) from by omega,
    hwrite', vyperAnchor?, hanchor, EvalResult.ofOption, bind, EvalResult.bind]

/-- `arr.push(v)` at or beyond the capacity reverts. -/
theorem pushArray_vyper_full {cfg : Config} {layout : StorageLayout} {bounds : VyperBounds}
    {stele : Frame} {evm : EVM.State} {slot : StorageRef} {er : EvaledStorageRef}
    {elem : StorageType} {cap : Nat} {s : UInt256} {v : Value}
    (hbase : stele.locals.get? slot.base = none)
    (her : evalStorageRef cfg stele evm slot = .ok er)
    (hty : storageTypeAt? stele.contract.storage er = some (.dynamicArray elem))
    (hbackend : cfg.storageBackend = vyperStorageBackend layout bounds)
    (hcheck : vyperCheckRef? layout bounds evm er = .ok ())
    (hbounds : bounds er = some (.dynamic cap)) (hanchor : layout er = some (.anchor s))
    (hcap : cap ≤ (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner s).toNat)
    (hnotrans : usesTransientStorage stele slot = false) :
    pushArray? cfg stele evm slot (some v) = .revert := by
  simp only [pushArray?, hnotrans, Bool.false_eq_true, if_false, resolveStorageRef?_ok hbase her hty,
    bind, EvalResult.bind, hbackend, vyperStorageBackend, vyperPushStorage?, hcheck,
    vyperLength_ok hbounds hanchor, hbounds, pure]
  simp [hcap]

/-- `arr.pop()` of a nonempty array only lowers the length word. -/
theorem popArray_vyper_ok {cfg : Config} {layout : StorageLayout} {bounds : VyperBounds}
    {stele : Frame} {evm : EVM.State} {slot : StorageRef} {er : EvaledStorageRef}
    {elem : StorageType} {cap : Nat} {s : UInt256}
    (hbase : stele.locals.get? slot.base = none)
    (her : evalStorageRef cfg stele evm slot = .ok er)
    (hty : storageTypeAt? stele.contract.storage er = some (.dynamicArray elem))
    (hbackend : cfg.storageBackend = vyperStorageBackend layout bounds)
    (hcheck : vyperCheckRef? layout bounds evm er = .ok ())
    (hbounds : bounds er = some (.dynamic cap)) (hanchor : layout er = some (.anchor s))
    (hpos : 0 < (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner s).toNat)
    (hnotrans : usesTransientStorage stele slot = false) :
    popArray? cfg stele evm slot =
      .ok (Stele.EVM.storageStore evm evm.executionEnv.codeOwner s
        (UInt256.ofNat ((Stele.EVM.storageLoad evm evm.executionEnv.codeOwner s).toNat - 1))) := by
  simp only [popArray?, hnotrans, Bool.false_eq_true, if_false, resolveStorageRef?_ok hbase her hty,
    bind, EvalResult.bind, hbackend, vyperStorageBackend, vyperPopStorage?, hcheck,
    vyperLength_ok hbounds hanchor, pure]
  simp [show (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner s).toNat ≠ 0 from by omega,
    vyperAnchor?, hanchor, EvalResult.ofOption, bind, EvalResult.bind]

/-! ## Structs of three scalar fields, and generic reads/writes through the backend -/

theorem vyperReadRaw_struct3 {layout : StorageLayout} {bounds : VyperBounds} {evm : EVM.State}
    {er : EvaledStorageRef} {n : Ident} {f1 f2 f3 : Ident} {t1 t2 t3 : ElemType} {l1 l2 l3 : StorageLoc}
    (h1 : layout { er with steps := er.steps ++ [.field f1] } = some (.leaf l1))
    (h2 : layout { er with steps := er.steps ++ [.field f2] } = some (.leaf l2))
    (h3 : layout { er with steps := er.steps ++ [.field f3] } = some (.leaf l3)) :
    vyperReadRaw? layout bounds evm er (.struct n [(f1, .elem t1), (f2, .elem t2), (f3, .elem t3)]) =
      .ok (.struct n [(f1, storageLocLoad evm l1), (f2, storageLocLoad evm l2), (f3, storageLocLoad evm l3)]) := by
  simp [vyperReadRaw?, vyperReadFields?, vyperLeafLoc?, h1, h2, h3, bind, EvalResult.bind, EvalResult.ofOption, pure]

theorem vyperWriteRaw_struct3 {layout : StorageLayout} {bounds : VyperBounds} {evm evm1 evm2 evm3 : EVM.State}
    {er : EvaledStorageRef} {n : Ident} {f1 f2 f3 : Ident} {t1 t2 t3 : ElemType} {l1 l2 l3 : StorageLoc}
    {v1 v2 v3 : Value}
    (h1 : layout { er with steps := er.steps ++ [.field f1] } = some (.leaf l1))
    (h2 : layout { er with steps := er.steps ++ [.field f2] } = some (.leaf l2))
    (h3 : layout { er with steps := er.steps ++ [.field f3] } = some (.leaf l3))
    (hs1 : storageLocStore evm l1 v1 = some evm1) (hs2 : storageLocStore evm1 l2 v2 = some evm2)
    (hs3 : storageLocStore evm2 l3 v3 = some evm3) :
    vyperWriteRaw? layout bounds evm er (.struct n [(f1, .elem t1), (f2, .elem t2), (f3, .elem t3)])
      (.struct n [(f1, v1), (f2, v2), (f3, v3)]) = .ok evm3 := by
  simp [vyperWriteRaw?, vyperWriteFields?, vyperLeafLoc?, h1, h2, h3, hs1, hs2, hs3, bind, EvalResult.bind,
    EvalResult.ofOption, pure]

/-- Any storage read through the Vyper backend, from a raw-reader fact. -/
theorem evalExpr_storage_vyper_of_read {cfg : Config} {layout : StorageLayout} {bounds : VyperBounds}
    {stele : Frame} {evm : EVM.State} {slot : StorageRef} {er : EvaledStorageRef} {ty : StorageType} {v : Value}
    (hbase : stele.locals.get? slot.base = none)
    (her : evalStorageRef cfg stele evm slot = .ok er)
    (hty : storageTypeAt? stele.contract.storage er = some ty)
    (hbackend : cfg.storageBackend = vyperStorageBackend layout bounds)
    (hcheck : vyperCheckRef? layout bounds evm er = .ok ())
    (hread : vyperReadRaw? layout bounds evm er ty = .ok v) :
    evalExpr? cfg stele evm (.storage slot) = .ok v := by
  rw [evalExpr?]
  simp only [resolveStorageRef?_ok hbase her hty, bind, EvalResult.bind, hbackend, vyperStorageBackend, hcheck, hread]

/-- Any storage write through the Vyper backend, from a raw-writer fact. -/
theorem assignStorageRef_storage_vyper_of_write {cfg : Config} {layout : StorageLayout} {bounds : VyperBounds}
    {stele : Frame} {evm evm' : EVM.State} {slot : StorageRef} {er : EvaledStorageRef} {ty : StorageType} {v : Value}
    (hbase : stele.locals.get? slot.base = none)
    (her : evalStorageRef cfg stele evm slot = .ok er)
    (hty : storageTypeAt? stele.contract.storage er = some ty)
    (hbackend : cfg.storageBackend = vyperStorageBackend layout bounds)
    (hcheck : vyperCheckRef? layout bounds evm er = .ok ())
    (hwrite : vyperWriteRaw? layout bounds evm er ty v = .ok evm') :
    assignStorageRef? cfg stele evm .storage slot v = .ok (stele, evm') := by
  apply assignStorageRef_storage_of_write hbase her hty
  rw [hbackend]
  simp [vyperStorageBackend, hcheck, hwrite, bind, EvalResult.bind]

/-- A field of a local struct value. -/
theorem evalExpr_field_local {cfg : Config} {stele : Frame} {evm : EVM.State} {name f : Ident}
    {n : Ident} {fields : List (Ident × Value)} {v : Value}
    (hL : stele.locals.get? name = some (.struct n fields)) (hf : lookupAssoc fields f = some v) :
    evalExpr? cfg stele evm (.field (.var name) f) = .ok v := by
  rw [evalExpr?, evalExpr?]
  show (do
      let baseValue ← EvalResult.ofOption EvalError.unboundVariable (stele.locals.get? name)
      match baseValue with
      | .storageRef er ty => do
          let step := EvaledStorageRefStep.field f
          let ty' ← EvalResult.ofOption .typeError (storageTypeStep? ty step)
          cfg.storageBackend.read { er with steps := er.steps ++ [step] } ty' evm
      | _ => EvalResult.ofOption .typeError (lookupField? baseValue f)) = _
  rw [Std.HashMap.get?_eq_getElem?] at hL
  simp [hL, EvalResult.ofOption, bind, EvalResult.bind, lookupField?, hf]

end Reasoning.VyperBounded
