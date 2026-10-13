import Tests.Pipeline.VyperVault.Dispatch
import Reasoning.Immutables

/-!
# VyperVault proof helpers

Hand-written facts shared by the function proofs: the typed-storage precondition (Vyper returns
storage words unnormalized), the immutable `OWNER` as a value and as the code suffix, the frame
the bodies run in, and the view of a storage word at the initial state.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperImmutables

namespace Tests.Pipeline.VyperVault

set_option maxRecDepth 2000000

/-- Typed storage: the `paused` slot (4) holds a `bool` word, `0` or `1`.  Vyper writes it from a
validated calldata bool and returns it unnormalized, so this is the precondition under which the
spec's `bool` view is the bytecode's word. -/
def storageWF : StorageWF := fun σ I =>
  solcSlotWordAt (UInt256.ofNat 4) σ I = ⟨0⟩ ∨ solcSlotWordAt (UInt256.ofNat 4) σ I = ⟨1⟩

/-- The frame of a transition body run with the deployed immutables. -/
abbrev frame (imms locals : Store) : Frame :=
  { contract := contract, locals := locals, immutables := restrictImmutables contract imms }

theorem owner_of_fit {imms : Store} (h : immutablesFit contract imms) :
    ∃ a : AccountAddress, imms.get? "OWNER" = some (.address a) := by
  obtain ⟨v, hget, hfits⟩ := h ⟨"OWNER", .address⟩ (by decide)
  cases v <;> simp [elemValueFits] at hfits
  exact ⟨_, hget⟩

theorem wordsOf_OWNER {imms : Store} {a : AccountAddress}
    (hget : imms.get? "OWNER" = some (.address a)) :
    wordsOf imms "OWNER" = EVM.Word.ofNat a.toNat := by
  unfold wordsOf
  rw [hget]
  simp [scalarBytes?, valueToWord, uInt256OfByteArray_toByteArray]

/-- The immutable section is the single word of `OWNER`. -/
theorem suffixWords_OWNER (w : String → UInt256) :
    immutableLayout.suffixWords w = (w "OWNER").toByteArray := by
  have hslots : immutableLayout.slots.map (fun slot => (slot.offset, (w slot.name).toByteArray)) =
      [] ++ (0, (w "OWNER").toByteArray) :: [] := by rfl
  have hpatch : ∃ suffix, Stele.patchRuntime (ByteArray.zeroes immutableLayout.size)
      (immutableLayout.slots.map (fun slot => (slot.offset, (w slot.name).toByteArray))) =
      some suffix := by
    simp only [immutableLayout, List.map_cons, List.map_nil]
    simp [Stele.patchRuntime, Stele.spliceBytes?, ByteArray.size_append,
      ByteArray.size_extract, ByteArray_zeroes_size, toByteArray_size]
  have h := Layout.suffixWords_read_slot (layout := immutableLayout) (words := w) (name := "OWNER")
    (offset := 0) (pre := []) (post := []) hslots (by decide) (by intro p hp; simp at hp) hpatch
  have hsize : (immutableLayout.suffixWords w).size = 32 := Layout.suffixWords_size _ _
  rw [readWithPadding_eq_extract _ _ (by rw [hsize]), Nat.zero_add, ← hsize,
    byteArray_extract_self] at h
  exact h

theorem evalImmutable_OWNER {imms : Store} {a : AccountAddress}
    (hget : imms.get? "OWNER" = some (.address a)) (locals : Store) (evm : EVM.State) :
    evalExpr? config (frame imms locals) evm (.immutable "OWNER") = .ok (.address a) := by
  simp only [evalExpr?, frame]
  rw [Reasoning.Immutables.restrictImmutables_get? (contract := contract) (n := "OWNER") (by decide), hget]
  rfl

/-- The storage word the summaries read is the layout word of the initial account map. -/
theorem slotWord_eq (σ : AccountMap) (I : ExecutionEnv) (slot : UInt256) :
    (σ.get? I.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac => ac.storage.getD slot ⟨0⟩)) =
      solcSlotWordAt slot σ I := rfl


/-! ## Entry guards and the first argument -/

/-- The first calldata word as the bytecode loads it. -/
abbrev argWord (I : ExecutionEnv) : UInt256 :=
  uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32)

theorem argWord_eq (I : ExecutionEnv) : argWord I = calldataWord I.calldata 4 := by
  show uInt256OfByteArray (I.calldata.readBytes (UInt256.ofNat 4).toNat 32) = _
  rw [ulit_toNat' 4 (by decide)]

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

theorem guard_wv {I : ExecutionEnv} {x : UInt256} (hwv : I.weiValue ≠ ⟨0⟩) :
    UInt256.lor I.weiValue x ≠ UInt256.ofNat 0 := by
  rw [u256_lor_comm]; exact u256_lor_ne_zero_right hwv

/-! ## Memory of an address-keyed mapping access (`balances[arg]`) -/

/-- The argument word stored at offset 64 after the dispatch of bucket `m`. -/
abbrev argMem (m : Nat) (w : UInt256) : ByteArray :=
  w.toByteArray.write 0 (vyperVaultDispatchMem m) (UInt256.ofNat 64).toNat 32

theorem argMem_size (m : Nat) (w : UInt256) (hmem : (vyperVaultDispatchMem m).size = 32) :
    (argMem m w).size = 96 := by
  unfold argMem
  rw [ulit_toNat' 64 (by decide),
    toByteArray_write_eq _ _ _ (by rw [hmem]; omega) (by rw [hmem]; exact lt_usize 32 (by norm_num)),
    ByteArray.size_append, ByteArray.size_append, hmem, ByteArray_zeroes_size, toByteArray_size]

theorem memLoad_argMem (m : Nat) (w : UInt256) (hmem : (vyperVaultDispatchMem m).size = 32) :
    memLoad (UInt256.ofNat 64) (argMem m w) = w := by
  unfold memLoad
  rw [ulit_toNat' 64 (by decide), if_neg (by rw [argMem_size m w hmem]; omega)]
  unfold argMem
  rw [ulit_toNat' 64 (by decide),
    toByteArray_write_read_back_of_gap _ _ _ (by rw [hmem]; exact lt_usize 32 (by norm_num)),
    fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

/-- `keccak256(slot ++ key)` of the scratch memory the bytecode builds: `vyperMappingSlot`. -/
theorem keccak_argMem (m : Nat) (w : UInt256) (hmem : (vyperVaultDispatchMem m).size = 32)
    (hcanon : w.toNat < EVM.addressModulus) :
    keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64)
      (wordAt0Mem (UInt256.ofNat 1) (wordAt32Mem (memLoad (UInt256.ofNat 64) (argMem m w)) (argMem m w))) =
      vyperMappingSlot (UInt256.ofNat 1) (.address (AccountAddress.ofNat w.toNat)) := by
  unfold keccakWord
  rw [memLoad_argMem m w hmem, show (⟨0⟩ : UInt256).toNat = 0 from rfl, ulit_toNat' 64 (by decide)]
  have h := wordAt0Mem_wordAt32Mem_vyperMappingSlot (UInt256.ofNat 1)
    (.address (AccountAddress.ofNat w.toNat)) (mem := argMem m w) (by rw [argMem_size m w hmem]; omega)
  rwa [keyValueToWord_address_of_canonical w hcanon] at h

/-! ## Frame-generic evaluation -/

/-- The contract's own balance as the `SELFBALANCE` summary spells it. -/
abbrev selfBalanceWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  (σ.get? I.codeOwner |>.elim ⟨0⟩ (·.balance))

theorem evalSelfbalance {σ σ₀ A I} {g : Sat256} (imms L : Store) :
    evalExpr? config (frame imms L) (initState σ σ₀ g A I) (.env .selfbalance) =
      .ok (.int (Int.ofNat (selfBalanceWord σ I).toNat)) := by
  rw [evalExpr?]
  show EvalResult.ok (Value.int (Int.ofNat ((σ.get? I.codeOwner).option (EVM.Word.ofNat 0) (·.balance)).toNat)) = _
  unfold selfBalanceWord
  cases σ.get? I.codeOwner <;> rfl

theorem evalVar (imms L : Store) (evm : EVM.State) (name : Ident) (v : Value)
    (h : L.get? name = some v) : evalExpr? config (frame imms L) evm (.var name) = .ok v := by
  rw [evalExpr?]
  show EvalResult.ofOption _ (L.get? name) = _
  rw [h]; rfl

theorem evalIte (imms L : Store) (evm : EVM.State) {cond thenE elseE : Expr} {b : Bool} {v : Value}
    (hcond : evalExpr? config (frame imms L) evm cond = .ok (.bool b))
    (hthen : b = true → evalExpr? config (frame imms L) evm thenE = .ok v)
    (helse : b = false → evalExpr? config (frame imms L) evm elseE = .ok v) :
    evalExpr? config (frame imms L) evm (.ite cond thenE elseE) = .ok v := by
  cases b
  · simp [evalExpr?, EvalResult.bind, bind, hcond, helse rfl]
  · simp [evalExpr?, EvalResult.bind, bind, hcond, hthen rfl]

theorem evalLtVars (imms L : Store) (evm : EVM.State) (x y : Ident) (a b : UInt256)
    (hx : L.get? x = some (.int (Int.ofNat a.toNat))) (hy : L.get? y = some (.int (Int.ofNat b.toNat))) :
    evalExpr? config (frame imms L) evm (.binary .lt (.var x) (.var y)) =
      .ok (.bool (decide (a.toNat < b.toNat))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), evalVar imms L evm x _ hx, evalVar imms L evm y _ hy]
  simp [EvalResult.bind, bind, evalBinaryOp?]

/-- The owner check `msg.sender == OWNER`. -/
theorem evalCallerEqOwner {σ σ₀ A I} {g : Sat256} {imms : Store} {a : AccountAddress}
    (hget : imms.get? "OWNER" = some (.address a)) (L : Store) :
    evalExpr? config (frame imms L) (initState σ σ₀ g A I)
      (.binary .eq (.env .caller) (.immutable "OWNER")) = .ok (.bool (decide (I.source = a))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), evalImmutable_OWNER hget]
  have hc : evalExpr? config (frame imms L) (initState σ σ₀ g A I) (.env .caller) =
      .ok (.address I.source) := by
    rw [evalExpr?]; rfl
  rw [hc]
  simp only [EvalResult.bind, bind, evalBinaryOp?]
  rw [value_address_beq]

/-- A word read above a 32-byte write at offset 0 (the `OWNER` scratch word) is unchanged. -/
theorem memLoad64_write0 (src M : ByteArray) (hsrc : 32 ≤ src.size) (hM : M.size = 96) :
    memLoad (UInt256.ofNat 64) (src.write 0 M (⟨0⟩ : UInt256).toNat 32) =
      memLoad (UInt256.ofNat 64) M := by
  have h0 : (⟨0⟩ : UInt256).toNat = 0 := rfl
  rw [h0]
  unfold memLoad
  rw [ulit_toNat' 64 (by decide), byteArray_write_size_of_inBounds _ _ _ _ hsrc (by omega),
    write32_read_above src M 0 64 hsrc (by omega) (by omega) (by omega)]

/-- The owner check on any EVM state. -/
theorem evalCallerEqOwner' {imms : Store} {a : AccountAddress}
    (hget : imms.get? "OWNER" = some (.address a)) (L : Store) (evm : EVM.State) :
    evalExpr? config (frame imms L) evm (.binary .eq (.env .caller) (.immutable "OWNER")) =
      .ok (.bool (decide (evm.executionEnv.source = a))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), evalImmutable_OWNER hget, evalExpr_caller]
  simp only [EvalResult.bind, bind, evalBinaryOp?]
  rw [value_address_beq]

end Tests.Pipeline.VyperVault
