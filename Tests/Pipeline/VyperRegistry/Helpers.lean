import Tests.Pipeline.VyperRegistry.Dispatch
import Reasoning.VyperBounded

/-!
# Registry proof helpers

Hand-written facts shared by the function proofs: the typed-storage precondition (Vyper returns
storage words unnormalized and the bounded backend rejects corrupted length words), the frame the
bodies run in, the per-function guards, the owner check routine, and the view of storage words
and mapping slots at the initial state.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperBounded

namespace Tests.Pipeline.VyperRegistry

set_option maxRecDepth 2000000

/-- The slot of `entries[id]` for a `uint256` key word. -/
abbrev entrySlot (id : UInt256) : UInt256 := vyperMappingSlot (UInt256.ofNat 1) (.int (Int.ofNat id.toNat))

/-- Typed storage: `ownable_owner` (slot 0) and every `entries[id].account` hold address words,
and every `entries[id].active` is a `bool` word.  Vyper returns these words unnormalized.  The
`ids` length word needs no clause: the backend reads it raw, as the bytecode does. -/
def storageWF : StorageWF := fun σ I =>
  (solcSlotWordAt ⟨0⟩ σ I).toNat < EVM.addressModulus ∧
  (∀ id : UInt256, (solcSlotWordAt (entrySlot id) σ I).toNat < EVM.addressModulus ∧
    (solcSlotWordAt (entrySlot id + UInt256.ofNat 2) σ I = ⟨0⟩ ∨
      solcSlotWordAt (entrySlot id + UInt256.ofNat 2) σ I = ⟨1⟩))

/-- The frame of a transition body run (no immutables). -/
abbrev frame (locals : Store) : Frame := { contract := contract, locals := locals }

/-- The storage word the summaries read is the layout word of the account map. -/
theorem slotWord_eq (σ : AccountMap) (I : ExecutionEnv) (slot : UInt256) :
    (σ.get? I.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD slot ⟨0⟩)) =
      solcSlotWordAt slot σ I := rfl

abbrev argWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32)
abbrev argWord2 (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 36).toNat 32)

theorem argWord_eq (I : ExecutionEnv) : argWord I = calldataWord I.calldata 4 := by
  show uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32) = _
  rw [ulit_toNat' 4 (by decide)]

theorem argWord2_eq (I : ExecutionEnv) : argWord2 I = calldataWord I.calldata 36 := by
  show uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 36).toNat 32) = _
  rw [ulit_toNat' 36 (by decide)]

theorem guard_ok {I : ExecutionEnv} (hwv : I.weiValue = ⟨0⟩) (hsz : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    UInt256.lor I.weiValue (UInt256.lt (UInt256.ofNat I.calldata.size) (UInt256.ofNat 36)) =
      UInt256.ofNat 0 := by
  rw [hwv, calldataSizeGuardOk hsz hsize]; decide

theorem guard_short {I : ExecutionEnv} (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 36) :
    UInt256.lor I.weiValue (UInt256.lt (UInt256.ofNat I.calldata.size) (UInt256.ofNat 36)) ≠
      UInt256.ofNat 0 := by
  rw [calldataSizeGuardShort hsize (by decide) hshort]
  exact u256_lor_ne_zero_right (by decide)

theorem guard68_ok {I : ExecutionEnv} (hwv : I.weiValue = ⟨0⟩) (hsz : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    UInt256.lor I.weiValue (UInt256.lt (UInt256.ofNat I.calldata.size) (UInt256.ofNat 68)) =
      UInt256.ofNat 0 := by
  rw [hwv, calldataSizeGuardOk hsz hsize]; decide

theorem guard68_short {I : ExecutionEnv} (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68) :
    UInt256.lor I.weiValue (UInt256.lt (UInt256.ofNat I.calldata.size) (UInt256.ofNat 68)) ≠
      UInt256.ofNat 0 := by
  rw [calldataSizeGuardShort hsize (by decide) hshort]
  exact u256_lor_ne_zero_right (by decide)

theorem guard_wv {I : ExecutionEnv} {x : UInt256} (hwv : I.weiValue ≠ ⟨0⟩) :
    UInt256.lor I.weiValue x ≠ UInt256.ofNat 0 := by
  rw [u256_lor_comm]; exact u256_lor_ne_zero_right hwv

/-! ## Mapping slots of `uint256` keys over the 32-byte dispatcher memory -/

theorem dispatchMem_size (m : Nat) (hm : m < 10) : (registryDispatchMem m).size = 32 := by
  interval_cases m <;> native_decide

/-- `keccak256(1 ++ key)` of the scratch memory built over the dispatcher memory. -/
theorem keccak_entry (m : Nat) (hm : m < 10) (w : UInt256) :
    keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64)
      ((UInt256.ofNat 1).toByteArray.write 0 (w.toByteArray.write 0 (registryDispatchMem m) 32 32) 0 32) =
      entrySlot w := by
  have h := keccakWord_hash32 (UInt256.ofNat 1) (.int (Int.ofNat w.toNat)) (registryDispatchMem m)
    (dispatchMem_size m hm)
  simp only [keyValueToWord, wordOfInt_ofNat_toNat] at h
  exact h

/-! ## Address words -/

/-- A canonical owner word equals the caller's word exactly when the caller is that address. -/
theorem addr_eq_iff_word {a : AccountAddress} {w : UInt256} (hcanon : w.toNat < EVM.addressModulus) :
    (a = AccountAddress.ofNat w.toNat) ↔ (UInt256.ofNat a.val = w) := by
  constructor
  · intro h
    subst h
    have h2 := keyValueToWord_address_of_canonical w hcanon
    rw [Reasoning.Theory.keyValueToWord_address] at h2
    exact h2
  · intro h
    rw [← h, ulit_toNat' _ (lt_trans a.isLt (by decide)), accountAddress_ofNat_val]

/-! ## Calldata decoding of one `uint256` -/

theorem decodeMode_uint256_ok (name : Ident) (cd : ByteArray) (hsz36 : 36 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.vyper [name] [abiUInt256] cd =
      some ((∅ : Store).insert name (uint256Value (calldataWord cd 4))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]; omega
  have hword4 : ABI.bytesToWord ((cd.toList.drop 4).take 32) = calldataWord cd 4 :=
    decode_word_at_eq cd 4 (by omega) (by norm_num)
  rw [decodeCalldataWithMode_vyperScalarWords_eq (by decide), if_neg (by rw [htlen]; omega),
    decodeScalarWords_uint256_ok htake4]
  simp [decodeCalldata.insertValues, hword4] <;> rfl

theorem decodeMode_uint256_none_short (name : Ident) (cd : ByteArray) (hsz : 4 ≤ cd.size)
    (hshort : cd.size < 36) :
    decodeCalldataWithMode DecodeMode.vyper [name] [abiUInt256] cd = none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [decodeCalldataWithMode_vyperScalarWords_eq (by decide), if_neg (by rw [htlen]; omega),
    decodeScalarWords_uint256_none_short (by rw [List.length_drop, htlen]; omega)]

/-- The data slot of `ids[i]` as the layout spells it and as the bytecode computes it. -/
theorem idsSlot_eq (w : UInt256) :
    UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat ((keyValueToWord (.int (Int.ofNat w.toNat))).toNat * 1) =
      UInt256.ofNat 3 + w := by
  simp only [keyValueToWord, wordOfInt_ofNat_toNat, Nat.mul_one, u256_ofNat_toNat]
  rw [show (UInt256.ofNat 2 + UInt256.ofNat 1 : UInt256) = UInt256.ofNat 3 from by decide]

/-- A plain local variable. -/
theorem evalVar (L : Store) (evm : EVM.State) (name : Ident) (v : Value) (h : L.get? name = some v) :
    evalExpr? config (frame L) evm (.var name) = .ok v := by
  rw [evalExpr?]
  show EvalResult.ofOption _ (L.get? name) = _
  rw [h]; rfl

/-- The length of `ids` through the backend, at the initial state. -/
theorem idsLength_initState {σ σ₀ A I} {g : UInt256} :
    config.storageBackend.length { base := "ids", steps := [] }
      (.dynamicArray (.elem (.int (.uint ⟨256, by decide⟩)))) (initState σ σ₀ (Sat256.ofUInt256 g) A I) =
      .ok (solcSlotWordAt (UInt256.ofNat 2) σ I).toNat := by
  rw [← storageLoad_initState_ofUInt256_solcSlotWordAt (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (UInt256.ofNat 2)]
  exact vyperStorageLength_dynamic (elem := .elem (.int (.uint ⟨256, by decide⟩))) (hcheck := rfl) (hbounds := rfl)
    (hanchor := rfl)

/-- The word of the address a canonical word denotes is the word itself. -/
theorem word_roundtrip {w : UInt256} (hcanon : w.toNat < EVM.addressModulus) :
    UInt256.ofNat (AccountAddress.ofNat w.toNat).val = w := by
  have h := keyValueToWord_address_of_canonical w hcanon
  rw [Reasoning.Theory.keyValueToWord_address] at h
  exact h

/-! ## The owner check `ownable__check_owner` -/

abbrev ownerRef : StorageRef := { base := "ownable_owner", steps := [] }

def checkOwnerCallee : CallableDecl :=
  { params := [], returnType := [],
    body := [.require (.binary .eq (.env .caller) (.storage ownerRef))] }

theorem checkOwnerCallee_lookup : lookupCallable? contract "ownable__check_owner" = some checkOwnerCallee := by rfl

/-- The owner word as the spec reads it. -/
theorem evalOwnerRead {L : Store} (evm : EVM.State) (hL : L.get? "ownable_owner" = none) :
    evalExpr? config (frame L) evm (.storage ownerRef) =
      .ok (.address (AccountAddress.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat)) := by
  rw [evalExpr_storage_vyper_scalar (hbackend := rfl) (hcheck := by rfl) (t := .address)
      (er := { base := "ownable_owner", steps := [] })
      (loc := vyperWordLoc ⟨0⟩ .address) (hbase := hL)
      (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by show storageTypeAt? contract.storage _ = _; decide) (hloc := rfl),
    storageLocLoad_vyperWord]
  rfl

/-- `msg.sender == ownable_owner`, decided on words for a canonical owner word. -/
theorem evalCallerEqOwner {L : Store} (evm : EVM.State) (hL : L.get? "ownable_owner" = none)
    (hcanon : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat < EVM.addressModulus) :
    evalExpr? config (frame L) evm (.binary .eq (.env .caller) (.storage ownerRef)) =
      .ok (.bool (decide (UInt256.ofNat evm.executionEnv.source.val =
        Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), evalOwnerRead evm hL, evalExpr_caller]
  simp only [EvalResult.bind, bind, evalBinaryOp?]
  rw [value_address_beq]
  congr 2
  exact decide_eq_decide.mpr (addr_eq_iff_word (a := evm.executionEnv.source) hcanon)

/-- `keccak256(1 ++ key)` of the scratch words written over a memory of at least 64 bytes. -/
theorem keccak_entry_over (M : ByteArray) (hM : 64 ≤ M.size) (w : UInt256) :
    keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64)
      ((UInt256.ofNat 1).toByteArray.write 0 (w.toByteArray.write 0 M 32 32) 0 32) = entrySlot w := by
  unfold keccakWord
  rw [show (⟨0⟩ : UInt256).toNat = 0 from rfl, ulit_toNat' 64 (by decide)]
  have h := wordAt0Mem_wordAt32Mem_vyperMappingSlot (UInt256.ofNat 1) (.int (Int.ofNat w.toNat)) (mem := M) hM
  simp only [keyValueToWord, wordOfInt_ofNat_toNat] at h
  exact h

/-- The evaluated reference of `entries[id]` (and of `entries[id].f`) for a `uint256` local. -/
theorem evalEntriesRef (L : Store) (evm : EVM.State) (w : UInt256) (name : Ident)
    (hL : L.get? name = some (uint256Value w)) :
    evalStorageRef config (frame L) evm { base := "entries", steps := [.mindex (.var name)] } =
      .ok { base := "entries", steps := [.mindex (.int (Int.ofNat w.toNat))] } := by
  rw [Std.HashMap.get?_eq_getElem?] at hL
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, hL]

theorem evalEntriesFieldRef (L : Store) (evm : EVM.State) (w : UInt256) (name f : Ident)
    (hL : L.get? name = some (uint256Value w)) :
    evalStorageRef config (frame L) evm { base := "entries", steps := [.mindex (.var name), .field f] } =
      .ok { base := "entries", steps := [.mindex (.int (Int.ofNat w.toNat)), .field f] } := by
  rw [Std.HashMap.get?_eq_getElem?] at hL
  simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure, evalExpr?, hL]

/-- The struct value of `entries[id]`. -/
abbrev entryValue (evm : EVM.State) (w : UInt256) : Value :=
  .struct "Entry"
    [("account", .address (AccountAddress.ofNat (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (entrySlot w)).toNat)),
     ("weight", uint256Value (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (entrySlot w + UInt256.ofNat 1))),
     ("active", wordToElem .bool (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (entrySlot w + UInt256.ofNat 2)))]

theorem evalEntriesRead (L : Store) (evm : EVM.State) (w : UInt256) (name : Ident)
    (hL : L.get? name = some (uint256Value w)) (hb : L.get? "entries" = none) :
    evalExpr? config (frame L) evm (.storage { base := "entries", steps := [.mindex (.var name)] }) =
      .ok (entryValue evm w) := by
  rw [evalExpr_storage_vyper_of_read (hbackend := rfl) (hcheck := by rfl) (hbase := hb)
      (er := { base := "entries", steps := [.mindex (.int (Int.ofNat w.toNat))] })
      (her := evalEntriesRef L evm w name hL) (hty := rfl)
      (hread := vyperReadRaw_struct3 (l1 := vyperWordLoc (entrySlot w) .address)
        (l2 := vyperUint256Loc (entrySlot w + UInt256.ofNat 1)) (l3 := vyperWordLoc (entrySlot w + UInt256.ofNat 2) .bool)
        rfl rfl rfl)]
  rw [storageLocLoad_vyperWord, storageLocLoad_vyperWord]
  erw [storageLocLoad_uint256]
  rfl

/-- `Entry(account=…, weight=…, active=True)` as a value. -/
theorem evalEntryLit (L : Store) (evm : EVM.State) (a : AccountAddress) (w : UInt256)
    (h1 : L.get? "account" = some (.address a)) (h2 : L.get? "weight" = some (uint256Value w)) :
    evalExpr? config (frame L) evm
      (.structLit "Entry" [("account", .var "account"), ("weight", .var "weight"), ("active", .boolLit true)]) =
      .ok (.struct "Entry" [("account", .address a), ("weight", uint256Value w), ("active", .bool true)]) := by
  have hb : evalExpr? config (frame L) evm (.boolLit true) = .ok (.bool true) := by rw [evalExpr?]; rfl
  rw [evalExpr?]
  simp only [evalStructFields?, evalVar L evm "account" _ h1, evalVar L evm "weight" _ h2, hb, bind, EvalResult.bind, pure]

/-- Writing `Entry(account, weight, True)` to `entries[id]`. -/
theorem assignEntry (L : Store) (evm : EVM.State) (id : UInt256) (a : AccountAddress) (w : UInt256)
    (hL : L.get? "id" = some (uint256Value id)) (hb : L.get? "entries" = none) :
    assignStorageRef? config (frame L) evm .storage { base := "entries", steps := [.mindex (.var "id")] }
      (.struct "Entry" [("account", .address a), ("weight", uint256Value w), ("active", .bool true)]) =
      .ok (frame L, Solm.EVM.storageStore (Solm.EVM.storageStore (Solm.EVM.storageStore evm
        evm.executionEnv.codeOwner (entrySlot id) (UInt256.ofNat a.val))
        evm.executionEnv.codeOwner (entrySlot id + UInt256.ofNat 1) w)
        evm.executionEnv.codeOwner (entrySlot id + UInt256.ofNat 2) (UInt256.ofNat 1)) := by
  apply assignStorageRef_storage_vyper_of_write (hbackend := rfl) (hcheck := by rfl) (hbase := hb)
    (er := { base := "entries", steps := [.mindex (.int (Int.ofNat id.toNat))] })
    (her := evalEntriesRef L evm id "id" hL) (hty := rfl)
  apply vyperWriteRaw_struct3 (l1 := vyperWordLoc (entrySlot id) .address)
    (l2 := vyperUint256Loc (entrySlot id + UInt256.ofNat 1)) (l3 := vyperWordLoc (entrySlot id + UInt256.ofNat 2) .bool)
    rfl rfl rfl (storageLocStore_vyperWord_address _ _ _)
  · erw [storageLocStore_uint256, storageStore_executionEnv]
  · rw [storageLocStore_vyperWord_value _ _ _ _ (UInt256.ofNat 1) rfl, storageStore_executionEnv,
      storageStore_executionEnv]

/-- `ids.push(v)` through the backend, below the capacity. -/
theorem pushIds (L : Store) (evm : EVM.State) (v : UInt256) (hb : L.get? "ids" = none)
    (hcap : (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 2)).toNat < 16) :
    pushArray? config (frame L) evm { base := "ids", steps := [] } (some (uint256Value v)) =
      .ok (Solm.EVM.storageStore
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat ((keyValueToWord (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 2)).toNat))).toNat * 1)) v)
        (Solm.EVM.storageStore evm evm.executionEnv.codeOwner
          (UInt256.ofNat 2 + UInt256.ofNat 1 + UInt256.ofNat ((keyValueToWord (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 2)).toNat))).toNat * 1)) v).executionEnv.codeOwner
        (UInt256.ofNat 2)
        (UInt256.ofNat ((Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (UInt256.ofNat 2)).toNat + 1))) :=
  pushArray_vyper_ok (hbackend := rfl) (hcheck := rfl) (hbounds := rfl) (hanchor := rfl) (hbase := hb)
    (er := { base := "ids", steps := [] }) (elem := .elem (.int (.uint ⟨256, by decide⟩)))
    (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (hty := by show storageTypeAt? contract.storage _ = _; decide) hcap
    (hwrite := vyperWriteRaw_elem (hloc := rfl) (storageLocStore_uint256 evm _ v)) (hnotrans := rfl)

end Tests.Pipeline.VyperRegistry
