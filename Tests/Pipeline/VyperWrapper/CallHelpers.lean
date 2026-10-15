import Tests.Pipeline.VyperWrapper.Helpers
import Reasoning.VyperCalls

/-!
# Wrapper external-call helpers

The ABI encodings of the four interface calls (`transferFrom`, `balanceOf`, `transfer`, `onWrap`)
as `externalABI.encode?` produces them, and the memory the bytecode builds for each call.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
  Reasoning.VyperCalls
open Reasoning.VyperImmutables

namespace Tests.Pipeline.VyperWrapper

set_option maxRecDepth 2000000

/-! ## ABI encodings -/

theorem encodeFrom_static_cons {ty : ABIType} {v : Value} {tys : List ABIType} {vs : List Value}
    {hs : Nat} {head tail bytes : List UInt8}
    (hdyn : isDynamicABIType ty = false) (henc : encodeABIValue? ty v = some bytes) :
    encodeABIValuesFrom? (ty :: tys) (v :: vs) hs head tail = encodeABIValuesFrom? tys vs hs (head ++ bytes) tail := by
  rw [encodeABIValuesFrom?]
  simp [henc, hdyn]

theorem encodeFrom_nil (hs : Nat) (head tail : List UInt8) :
    encodeABIValuesFrom? [] [] hs head tail = some (head ++ tail) := by
  rw [encodeABIValuesFrom?]

theorem encodeABIValue_address (a : AccountAddress) :
    encodeABIValue? (.elem .address) (.address a) = some (EVM.Word.toBytesBE (UInt256.ofNat a.val)) := by
  simp only [encodeABIValue?, encodeABIWord?, bind, Option.bind]
  rfl

/-- The word of an address argument, as the bytecode stacks it. -/
abbrev addrWord (a : AccountAddress) : UInt256 := UInt256.ofNat a.val

theorem encode_transferFrom (a b : AccountAddress) (n : UInt256) :
    config.externalABI.encode? "transferFrom" [.address a, .address b, uint256Value n] =
      some (selectorBytes 0x23 0xb8 0x72 0xdd ++ (addrWord a).toByteArray ++ (addrWord b).toByteArray ++ n.toByteArray) := by
  show ABI.encodeCallWithSelector? (selectorBytes 0x23 0xb8 0x72 0xdd) [.elem .address, .elem .address, abiUInt256]
    [.address a, .address b, uint256Value n] = _
  unfold ABI.encodeCallWithSelector? ABI.encodeABIValues?
  rw [abiTupleHeadSize_scalarWords_eq (by decide)]
  simp only [bind, Option.bind]
  rw [encodeFrom_static_cons rfl (encodeABIValue_address a), encodeFrom_static_cons rfl (encodeABIValue_address b),
    encodeFrom_static_cons rfl (encodeABIValue_uint256 n), encodeFrom_nil]
  simp only [List.nil_append, List.append_nil, list_toByteArray_append, word_toBytesBE_toByteArray_eq_toByteArray,
    ByteArray.append_assoc]

theorem encode_transfer (a : AccountAddress) (n : UInt256) :
    config.externalABI.encode? "transfer" [.address a, uint256Value n] =
      some (selectorBytes 0xa9 0x05 0x9c 0xbb ++ (addrWord a).toByteArray ++ n.toByteArray) := by
  show ABI.encodeCallWithSelector? (selectorBytes 0xa9 0x05 0x9c 0xbb) [.elem .address, abiUInt256]
    [.address a, uint256Value n] = _
  unfold ABI.encodeCallWithSelector? ABI.encodeABIValues?
  rw [abiTupleHeadSize_scalarWords_eq (by decide)]
  simp only [bind, Option.bind]
  rw [encodeFrom_static_cons rfl (encodeABIValue_address a), encodeFrom_static_cons rfl (encodeABIValue_uint256 n),
    encodeFrom_nil]
  simp only [List.nil_append, List.append_nil, list_toByteArray_append, word_toBytesBE_toByteArray_eq_toByteArray,
    ByteArray.append_assoc]

theorem encode_onWrap (a : AccountAddress) (n : UInt256) :
    config.externalABI.encode? "onWrap" [.address a, uint256Value n] =
      some (selectorBytes 0xa2 0x33 0x56 0xfa ++ (addrWord a).toByteArray ++ n.toByteArray) := by
  show ABI.encodeCallWithSelector? (selectorBytes 0xa2 0x33 0x56 0xfa) [.elem .address, abiUInt256]
    [.address a, uint256Value n] = _
  unfold ABI.encodeCallWithSelector? ABI.encodeABIValues?
  rw [abiTupleHeadSize_scalarWords_eq (by decide)]
  simp only [bind, Option.bind]
  rw [encodeFrom_static_cons rfl (encodeABIValue_address a), encodeFrom_static_cons rfl (encodeABIValue_uint256 n),
    encodeFrom_nil]
  simp only [List.nil_append, List.append_nil, list_toByteArray_append, word_toBytesBE_toByteArray_eq_toByteArray,
    ByteArray.append_assoc]

theorem encode_balanceOf (a : AccountAddress) :
    config.externalABI.encode? "balanceOf" [.address a] =
      some (selectorBytes 0x70 0xa0 0x82 0x31 ++ (addrWord a).toByteArray) := by
  show ABI.encodeCallWithSelector? (selectorBytes 0x70 0xa0 0x82 0x31) [.elem .address] [.address a] = _
  unfold ABI.encodeCallWithSelector? ABI.encodeABIValues?
  rw [abiTupleHeadSize_scalarWords_eq (by decide)]
  simp only [bind, Option.bind]
  rw [encodeFrom_static_cons rfl (encodeABIValue_address a), encodeFrom_nil]
  simp only [List.nil_append, List.append_nil, word_toBytesBE_toByteArray_eq_toByteArray]

/-- The return decoders of the spec's ABI (modern mode). -/
theorem decode_transferFrom (out : ByteArray) :
    config.externalABI.decode? "transferFrom" out = (ABI.decodeReturnValue? abiBool out).map (fun v => [v]) := rfl
theorem decode_transfer (out : ByteArray) :
    config.externalABI.decode? "transfer" out = (ABI.decodeReturnValue? abiBool out).map (fun v => [v]) := rfl
theorem decode_balanceOf (out : ByteArray) :
    config.externalABI.decode? "balanceOf" out = (ABI.decodeReturnValue? abiUInt256 out).map (fun v => [v]) := rfl
theorem decode_onWrap (out : ByteArray) : config.externalABI.decode? "onWrap" out = some [] := rfl

/-! ## Expression helpers -/

theorem evalExpr_eq_zero_word {cfg : Config} {stele : Frame} {evm : EVM.State} {e : Expr} {a : UInt256}
    (ha : evalExpr? cfg stele evm e = .ok (uint256Value a)) :
    evalExpr? cfg stele evm (.binary .eq e (.intLit 0)) = .ok (.bool (decide (a.toNat = 0))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), ha, evalExpr?]
  simp [EvalResult.bind, bind, evalBinaryOp?, uint256Value, value_int_beq]

theorem evalExpr_div_zero {cfg : Config} {stele : Frame} {evm : EVM.State} {lhs rhs : Expr} {a : UInt256}
    (ha : evalExpr? cfg stele evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg stele evm rhs = .ok (uint256Value ⟨0⟩)) :
    evalExpr? cfg stele evm (.binary .div lhs rhs) = .revert := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
  simp [EvalResult.bind, bind, evalBinaryOp?]

theorem wordsOf_TOKEN' {imms : Store} {a : AccountAddress} (hget : imms.get? "TOKEN" = some (.address a)) :
    wordsOf imms "TOKEN" = addrWord a := by
  rw [wordsOf_TOKEN hget]; rfl

/-! ## The memory of `balanceOf(self)` (pc 1527 and 1053): `TOKEN` at 0, the selector at 96, `self` at 128 -/

abbrev selB : UInt256 := UInt256.ofNat 1889567281
abbrev thisWord (I : ExecutionEnv) : UInt256 := UInt256.ofNat I.codeOwner.val
abbrev balMem (t : UInt256) (I : ExecutionEnv) (M0 : ByteArray) : ByteArray :=
  (thisWord I).toByteArray.write 0 (selB.toByteArray.write 0 (t.toByteArray.write 0 M0 0 32) 96 32) 128 32

theorem balMem_sizes (t : UInt256) (I : ExecutionEnv) (M0 : ByteArray) (hM0 : 32 ≤ M0.size ∧ M0.size ≤ 96) :
    (t.toByteArray.write 0 M0 0 32).size = M0.size ∧
    (selB.toByteArray.write 0 (t.toByteArray.write 0 M0 0 32) 96 32).size = 128 ∧
    (balMem t I M0).size = 160 := by
  have h0 : (t.toByteArray.write 0 M0 0 32).size = M0.size :=
    byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by omega)
  have h1 : (selB.toByteArray.write 0 (t.toByteArray.write 0 M0 0 32) 96 32).size = 128 :=
    toByteArray_write32_size_of_ge _ _ 96 M0.size 128 h0 hM0.2 (lt_usize _ (by omega)) rfl
  exact ⟨h0, h1, toByteArray_write32_size_of_ge _ _ 128 128 160 h1 (by omega) (lt_usize _ (by decide)) rfl⟩

theorem balMem_input (t : UInt256) (I : ExecutionEnv) (M0 : ByteArray) (hM0 : 32 ≤ M0.size ∧ M0.size ≤ 96) :
    (balMem t I M0).readWithPadding 124 36 = selectorBytes 0x70 0xa0 0x82 0x31 ++ (thisWord I).toByteArray := by
  obtain ⟨h0, h1, h2⟩ := balMem_sizes t I M0 hM0
  rw [show (36 : Nat) = 4 + 32 from rfl,
    byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by decide) (by rw [h2] <;> decide)]
  congr 1
  · rw [write32_read_below_len _ _ 128 124 4 (by rw [toByteArray_size]) (by rw [h1]) (by decide) (by rw [h1] <;> decide)
      (by decide) (by decide)]
    rw [show (124 : Nat) = 96 + 28 from rfl,
      toByteArray_write_read_window_of_gap _ _ 96 28 4 (by decide) (by decide) (by decide)
        (by rw [h0]; exact lt_usize _ (by omega))]
    native_decide
  · exact toByteArray_write_read_back_of_gap _ _ 128 (by rw [h1]; exact lt_usize _ (by decide))

/-! ## The caller's hash scratch `1 ++ caller` (for `shares[msg.sender]`) -/

abbrev callerWord (I : ExecutionEnv) : UInt256 := UInt256.ofNat I.source.val
abbrev hashMem (M : ByteArray) (I : ExecutionEnv) : ByteArray :=
  (UInt256.ofNat 1).toByteArray.write 0 ((callerWord I).toByteArray.write 0 M 32 32) 0 32

theorem hashMem_size32 (M : ByteArray) (I : ExecutionEnv) (hM : M.size = 32) : (hashMem M I).size = 64 := by
  have h1 : ((callerWord I).toByteArray.write 0 M 32 32).size = 64 :=
    toByteArray_write32_size_of_ge _ _ 32 32 64 hM (by omega) (lt_usize _ (by decide)) rfl
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [h1] <;> omega)]
  exact h1

theorem hashMem_size_ge (M : ByteArray) (I : ExecutionEnv) (hM : 64 ≤ M.size) : (hashMem M I).size = M.size := by
  have h1 : ((callerWord I).toByteArray.write 0 M 32 32).size = M.size :=
    byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by omega)
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [h1]; omega)]
  exact h1

theorem keccak_hashMem32 (M : ByteArray) (I : ExecutionEnv) (hM : M.size = 32) :
    keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) (hashMem M I) = sharesSlot I.source := by
  have h := keccakWord_hash32 (UInt256.ofNat 1) (.address I.source) M hM
  rw [Reasoning.Theory.keyValueToWord_address] at h
  exact h

theorem keccak_hashMem_ge (M : ByteArray) (I : ExecutionEnv) (hM : 64 ≤ M.size) :
    keccakWord (⟨0⟩ : UInt256) (UInt256.ofNat 64) (hashMem M I) = sharesSlot I.source :=
  keccak_caller_over M hM I

/-- Reads above the scratch see the underlying memory. -/
theorem hashMem_read_above (M : ByteArray) (I : ExecutionEnv) (r : Nat) (hr : 64 ≤ r) (hin : r + 32 ≤ M.size) :
    (hashMem M I).readWithPadding r 32 = M.readWithPadding r 32 := by
  have h1 : ((callerWord I).toByteArray.write 0 M 32 32).size = M.size :=
    byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by omega)
  rw [write32_read_above _ _ 0 r (by rw [toByteArray_size]) (by omega) (by omega) (by omega),
    write32_read_above _ _ 32 r (by rw [toByteArray_size]) (by omega) (by omega) (by omega)]

/-! ## The memory of `transfer(msg.sender, amount)` (pc 1209): `TOKEN` at 0, the selector at 160, the caller at 192, the amount at 224 -/

abbrev selT : UInt256 := UInt256.ofNat 2835717307
abbrev trMem (t : UInt256) (I : ExecutionEnv) (amt : UInt256) (M : ByteArray) : ByteArray :=
  amt.toByteArray.write 0 ((callerWord I).toByteArray.write 0
    (selT.toByteArray.write 0 (t.toByteArray.write 0 M 0 32) 160 32) 192 32) 224 32

theorem trMem_sizes (t : UInt256) (I : ExecutionEnv) (amt : UInt256) (M : ByteArray) (hM : M.size = 160) :
    (t.toByteArray.write 0 M 0 32).size = 160 ∧
    (selT.toByteArray.write 0 (t.toByteArray.write 0 M 0 32) 160 32).size = 192 ∧
    ((callerWord I).toByteArray.write 0 (selT.toByteArray.write 0 (t.toByteArray.write 0 M 0 32) 160 32) 192 32).size = 224 ∧
    (trMem t I amt M).size = 256 := by
  have h0 : (t.toByteArray.write 0 M 0 32).size = 160 := by
    rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [hM] <;> omega)]; exact hM
  have h1 := toByteArray_write32_size_of_ge _ selT 160 160 192 h0 (by omega) (lt_usize _ (by decide)) rfl
  have h2 := toByteArray_write32_size_of_ge _ (callerWord I) 192 192 224 h1 (by omega) (lt_usize _ (by decide)) rfl
  exact ⟨h0, h1, h2, toByteArray_write32_size_of_ge _ amt 224 224 256 h2 (by omega) (lt_usize _ (by decide)) rfl⟩

theorem trMem_input (t : UInt256) (I : ExecutionEnv) (amt : UInt256) (M : ByteArray) (hM : M.size = 160) :
    (trMem t I amt M).readWithPadding 188 68 =
      selectorBytes 0xa9 0x05 0x9c 0xbb ++ (callerWord I).toByteArray ++ amt.toByteArray := by
  obtain ⟨h0, h1, h2, h3⟩ := trMem_sizes t I amt M hM
  rw [show (68 : Nat) = 4 + (32 + 32) from rfl,
    byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by decide) (by rw [h3] <;> decide),
    byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by decide) (by rw [h3] <;> decide),
    ByteArray.append_assoc]
  congr 1
  · rw [write32_read_below_len _ _ 224 188 4 (by rw [toByteArray_size]) (by rw [h2]) (by decide) (by rw [h2] <;> decide)
      (by decide) (by decide),
      write32_read_below_len _ _ 192 188 4 (by rw [toByteArray_size]) (by rw [h1]) (by decide) (by rw [h1] <;> decide)
      (by decide) (by decide),
      show (188 : Nat) = 160 + 28 from rfl,
      toByteArray_write_read_window_of_gap _ _ 160 28 4 (by decide) (by decide) (by decide)
        (by rw [h0]; exact lt_usize _ (by decide))]
    native_decide
  congr 1
  · rw [write32_read_below _ _ 224 (188 + 4) (by rw [toByteArray_size]) (by rw [h2]) (by decide)]
    exact toByteArray_write_read_back_of_gap _ _ 192 (by rw [h1]; exact lt_usize _ (by decide))
  · exact toByteArray_write_read_back_of_gap _ _ 224 (by rw [h2]; exact lt_usize _ (by decide))

/-- The transfer's amount word, read back from the call memory (pc 1209 loads offset 96). -/
theorem trMem_pre_read96 (t : UInt256) (I : ExecutionEnv) (M : ByteArray) (hM : M.size = 160) :
    ((callerWord I).toByteArray.write 0 (selT.toByteArray.write 0 (t.toByteArray.write 0 M 0 32) 160 32) 192 32).readWithPadding 96 32 =
      M.readWithPadding 96 32 := by
  obtain ⟨h0, h1, h2, -⟩ := trMem_sizes t I ⟨0⟩ M hM
  rw [write32_read_below _ _ 192 96 (by rw [toByteArray_size]) (by rw [h1]) (by decide),
    write32_read_below _ _ 160 96 (by rw [toByteArray_size]) (by rw [h0]) (by decide),
    write32_read_above _ _ 0 96 (by rw [toByteArray_size]) (by omega) (by decide) (by rw [hM] <;> decide)]

theorem trMem_read96 (t : UInt256) (I : ExecutionEnv) (amt : UInt256) (M : ByteArray) (hM : M.size = 160) :
    (trMem t I amt M).readWithPadding 96 32 = M.readWithPadding 96 32 := by
  obtain ⟨-, -, h2, -⟩ := trMem_sizes t I amt M hM
  rw [write32_read_below _ _ 224 96 (by rw [toByteArray_size]) (by rw [h2]) (by decide), trMem_pre_read96 t I M hM]

/-! ## More expression helpers -/

/-- A local assignment, for any frame (the immutables are kept). -/
theorem assignLocalVar_frame {cfg : Config} {stele : Frame} {evm : EVM.State} {name : Ident} {old value : Value}
    (hget : stele.locals.get? name = some old) :
    assignStorageRef? cfg stele evm .localVar { base := name } value =
      .ok ({ stele with locals := stele.locals.insert name value }, evm) := by
  simp only [assignStorageRef?, updateLocalPath?, EvalResult.bind, bind, pure]
  change (match stele.locals.get? name with
    | some _ => EvalResult.ok (({ stele with locals := stele.locals.insert name value } : Frame), evm)
    | none => EvalResult.error EvalError.unboundVariable) = _
  rw [hget]

theorem evalExpr_gt_words {cfg : Config} {stele : Frame} {evm : EVM.State} {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg stele evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg stele evm rhs = .ok (uint256Value b)) :
    evalExpr? cfg stele evm (.binary .gt lhs rhs) = .ok (.bool (decide (b.toNat < a.toNat))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
  simp [EvalResult.bind, bind, evalBinaryOp?, uint256Value]

theorem evalExpr_and_false {cfg : Config} {stele : Frame} {evm : EVM.State} {lhs rhs : Expr}
    (hl : evalExpr? cfg stele evm lhs = .ok (.bool false)) :
    evalExpr? cfg stele evm (.binary .and lhs rhs) = .ok (.bool false) := by
  rw [evalExpr?, hl]; rfl

theorem evalExpr_and_true {cfg : Config} {stele : Frame} {evm : EVM.State} {lhs rhs : Expr} {b : Bool}
    (hl : evalExpr? cfg stele evm lhs = .ok (.bool true)) (hr : evalExpr? cfg stele evm rhs = .ok (.bool b)) :
    evalExpr? cfg stele evm (.binary .and lhs rhs) = .ok (.bool b) := by
  rw [evalExpr?, hl]
  simp only [bind, EvalResult.bind, hr]
  rfl

/-- `hook != address(0)` on a canonical hook word. -/
theorem evalHookNeZero (imms L : Store) (evm : EVM.State) (hL : L.get? "hook" = none)
    (hcanon : (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩).toNat < EVM.addressModulus) :
    evalExpr? config (frame imms L) evm (.binary .ne (.storage hookRef) (.cast (.intLit 0) (.elem .address))) =
      .ok (.bool (!decide (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩ = ⟨0⟩))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), evalHookRead imms L evm hL, evalAddrZero]
  simp only [EvalResult.bind, bind, evalBinaryOp?, value_address_beq, addrZero_iff_word hcanon]

/-! ## The memory of `transferFrom(msg.sender, self, amount)` (pc 354) -/

abbrev selF : UInt256 := UInt256.ofNat 599290589
abbrev tfMem (t : UInt256) (I : ExecutionEnv) (amt : UInt256) (M0 : ByteArray) : ByteArray :=
  amt.toByteArray.write 0 ((thisWord I).toByteArray.write 0 ((callerWord I).toByteArray.write 0
    (selF.toByteArray.write 0 (t.toByteArray.write 0 M0 0 32) 96 32) 128 32) 160 32) 192 32

theorem tfMem_sizes (t : UInt256) (I : ExecutionEnv) (amt : UInt256) (M0 : ByteArray) (hM0 : M0.size = 32) :
    (t.toByteArray.write 0 M0 0 32).size = 32 ∧
    (selF.toByteArray.write 0 (t.toByteArray.write 0 M0 0 32) 96 32).size = 128 ∧
    ((callerWord I).toByteArray.write 0 (selF.toByteArray.write 0 (t.toByteArray.write 0 M0 0 32) 96 32) 128 32).size = 160 ∧
    ((thisWord I).toByteArray.write 0 ((callerWord I).toByteArray.write 0
      (selF.toByteArray.write 0 (t.toByteArray.write 0 M0 0 32) 96 32) 128 32) 160 32).size = 192 ∧
    (tfMem t I amt M0).size = 224 := by
  have h0 : (t.toByteArray.write 0 M0 0 32).size = 32 := by
    rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [hM0] <;> omega)]; exact hM0
  have h1 := toByteArray_write32_size_of_ge _ selF 96 32 128 h0 (by omega) (lt_usize _ (by decide)) rfl
  have h2 := toByteArray_write32_size_of_ge _ (callerWord I) 128 128 160 h1 (by omega) (lt_usize _ (by decide)) rfl
  have h3 := toByteArray_write32_size_of_ge _ (thisWord I) 160 160 192 h2 (by omega) (lt_usize _ (by decide)) rfl
  exact ⟨h0, h1, h2, h3, toByteArray_write32_size_of_ge _ amt 192 192 224 h3 (by omega) (lt_usize _ (by decide)) rfl⟩

theorem tfMem_input (t : UInt256) (I : ExecutionEnv) (amt : UInt256) (M0 : ByteArray) (hM0 : M0.size = 32) :
    (tfMem t I amt M0).readWithPadding 124 100 =
      selectorBytes 0x23 0xb8 0x72 0xdd ++ (callerWord I).toByteArray ++ (thisWord I).toByteArray ++ amt.toByteArray := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := tfMem_sizes t I amt M0 hM0
  rw [show (100 : Nat) = 4 + (32 + (32 + 32)) from rfl,
    byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by decide) (by rw [h4] <;> decide),
    byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by decide) (by rw [h4] <;> decide),
    byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by decide) (by rw [h4] <;> decide),
    ByteArray.append_assoc, ByteArray.append_assoc]
  congr 1
  · rw [write32_read_below_len _ _ 192 124 4 (by rw [toByteArray_size]) (by rw [h3]) (by decide) (by rw [h3] <;> decide)
      (by decide) (by decide),
      write32_read_below_len _ _ 160 124 4 (by rw [toByteArray_size]) (by rw [h2]) (by decide) (by rw [h2] <;> decide)
      (by decide) (by decide),
      write32_read_below_len _ _ 128 124 4 (by rw [toByteArray_size]) (by rw [h1]) (by decide) (by rw [h1] <;> decide)
      (by decide) (by decide),
      show (124 : Nat) = 96 + 28 from rfl,
      toByteArray_write_read_window_of_gap _ _ 96 28 4 (by decide) (by decide) (by decide)
        (by rw [h0]; exact lt_usize _ (by decide))]
    native_decide
  congr 1
  · rw [write32_read_below _ _ 192 (124 + 4) (by rw [toByteArray_size]) (by rw [h3]) (by decide),
      write32_read_below _ _ 160 (124 + 4) (by rw [toByteArray_size]) (by rw [h2]) (by decide)]
    exact toByteArray_write_read_back_of_gap _ _ 128 (by rw [h1]; exact lt_usize _ (by decide))
  congr 1
  · rw [write32_read_below _ _ 192 (124 + 4 + 32) (by rw [toByteArray_size]) (by rw [h3]) (by decide)]
    exact toByteArray_write_read_back_of_gap _ _ 160 (by rw [h2]; exact lt_usize _ (by decide))
  · exact toByteArray_write_read_back_of_gap _ _ 192 (by rw [h3]; exact lt_usize _ (by decide))

/-! ## The memory of the second `balanceOf(self)` (pc 574): `amount` at 96, `TOKEN` at 0, the selector at 160, `self` at 192 -/

abbrev bal2Mem (t : UInt256) (I : ExecutionEnv) (amt : UInt256) (M : ByteArray) : ByteArray :=
  (thisWord I).toByteArray.write 0 (selB.toByteArray.write 0 (t.toByteArray.write 0 (amt.toByteArray.write 0 M 96 32) 0 32) 160 32) 192 32

theorem bal2Mem_sizes (t : UInt256) (I : ExecutionEnv) (amt : UInt256) (M : ByteArray) (hM : M.size = 256) :
    (amt.toByteArray.write 0 M 96 32).size = 256 ∧
    (t.toByteArray.write 0 (amt.toByteArray.write 0 M 96 32) 0 32).size = 256 ∧
    (selB.toByteArray.write 0 (t.toByteArray.write 0 (amt.toByteArray.write 0 M 96 32) 0 32) 160 32).size = 256 ∧
    (bal2Mem t I amt M).size = 256 := by
  have h0 : (amt.toByteArray.write 0 M 96 32).size = 256 := by
    rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [hM] <;> omega)]; exact hM
  have h1 : (t.toByteArray.write 0 (amt.toByteArray.write 0 M 96 32) 0 32).size = 256 := by
    rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [h0] <;> omega)]; exact h0
  have h2 : (selB.toByteArray.write 0 (t.toByteArray.write 0 (amt.toByteArray.write 0 M 96 32) 0 32) 160 32).size = 256 := by
    rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [h1] <;> omega)]; exact h1
  refine ⟨h0, h1, h2, ?_⟩
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [h2] <;> omega)]; exact h2

theorem bal2Mem_input (t : UInt256) (I : ExecutionEnv) (amt : UInt256) (M : ByteArray) (hM : M.size = 256) :
    (bal2Mem t I amt M).readWithPadding 188 36 = selectorBytes 0x70 0xa0 0x82 0x31 ++ (thisWord I).toByteArray := by
  obtain ⟨h0, h1, h2, h3⟩ := bal2Mem_sizes t I amt M hM
  rw [show (36 : Nat) = 4 + 32 from rfl,
    byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by decide) (by rw [h3] <;> decide)]
  congr 1
  · rw [write32_read_below_len _ _ 192 188 4 (by rw [toByteArray_size]) (by rw [h2] <;> omega) (by decide) (by rw [h2] <;> decide)
      (by decide) (by decide),
      show (188 : Nat) = 160 + 28 from rfl,
      toByteArray_write_read_window_of_gap _ _ 160 28 4 (by decide) (by decide) (by decide)
        (by rw [h1]; exact lt_usize _ (by decide))]
    native_decide
  · exact toByteArray_write_read_back_of_gap _ _ 192 (by rw [h2]; exact lt_usize _ (by decide))

theorem bal2Mem_read96 (t : UInt256) (I : ExecutionEnv) (amt : UInt256) (M : ByteArray) (hM : M.size = 256) :
    (bal2Mem t I amt M).readWithPadding 96 32 = amt.toByteArray := by
  obtain ⟨h0, h1, h2, -⟩ := bal2Mem_sizes t I amt M hM
  rw [write32_read_below _ _ 192 96 (by rw [toByteArray_size]) (by rw [h2] <;> omega) (by decide),
    write32_read_below _ _ 160 96 (by rw [toByteArray_size]) (by rw [h1] <;> omega) (by decide),
    write32_read_above _ _ 0 96 (by rw [toByteArray_size]) (by omega) (by decide) (by rw [h0] <;> decide)]
  exact toByteArray_write_read_back_of_gap _ _ 96 (by rw [hM]; exact lt_usize _ (by decide))

/-! ## A two-argument call written over a 256-byte memory: the selector at 160, the caller at 192, a word at 224 (pc 795/822) -/

abbrev callMem2 (sel : UInt256) (I : ExecutionEnv) (v : UInt256) (M : ByteArray) : ByteArray :=
  v.toByteArray.write 0 ((callerWord I).toByteArray.write 0 (sel.toByteArray.write 0 M 160 32) 192 32) 224 32

theorem callMem2_sizes (sel : UInt256) (I : ExecutionEnv) (v : UInt256) (M : ByteArray) (hM : M.size = 256) :
    (sel.toByteArray.write 0 M 160 32).size = 256 ∧
    ((callerWord I).toByteArray.write 0 (sel.toByteArray.write 0 M 160 32) 192 32).size = 256 ∧
    (callMem2 sel I v M).size = 256 := by
  have h1 : (sel.toByteArray.write 0 M 160 32).size = 256 := by
    rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [hM] <;> omega)]; exact hM
  have h2 : ((callerWord I).toByteArray.write 0 (sel.toByteArray.write 0 M 160 32) 192 32).size = 256 := by
    rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [h1] <;> omega)]; exact h1
  refine ⟨h1, h2, ?_⟩
  rw [byteArray_write_size_of_inBounds _ _ _ _ (by rw [toByteArray_size]) (by rw [h2] <;> omega)]; exact h2

theorem callMem2_input (sel : UInt256) (I : ExecutionEnv) (v : UInt256) (M : ByteArray) (hM : M.size = 256)
    (sb : ByteArray) (hsb : sel.toByteArray.extract 28 (28 + 4) = sb) :
    (callMem2 sel I v M).readWithPadding 188 68 = sb ++ (callerWord I).toByteArray ++ v.toByteArray := by
  obtain ⟨h1, h2, h3⟩ := callMem2_sizes sel I v M hM
  rw [show (68 : Nat) = 4 + (32 + 32) from rfl,
    byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by decide) (by rw [h3] <;> decide),
    byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by decide) (by rw [h3] <;> decide),
    ByteArray.append_assoc]
  congr 1
  · rw [write32_read_below_len _ _ 224 188 4 (by rw [toByteArray_size]) (by rw [h2] <;> omega) (by decide) (by rw [h2] <;> decide)
      (by decide) (by decide),
      write32_read_below_len _ _ 192 188 4 (by rw [toByteArray_size]) (by rw [h1] <;> omega) (by decide) (by rw [h1] <;> decide)
      (by decide) (by decide),
      show (188 : Nat) = 160 + 28 from rfl,
      toByteArray_write_read_window_of_gap _ _ 160 28 4 (by decide) (by decide) (by decide)
        (by rw [hM]; exact lt_usize _ (by decide))]
    exact hsb
  congr 1
  · rw [write32_read_below _ _ 224 (188 + 4) (by rw [toByteArray_size]) (by rw [h2] <;> omega) (by decide)]
    exact toByteArray_write_read_back_of_gap _ _ 192 (by rw [h1]; exact lt_usize _ (by decide))
  · exact toByteArray_write_read_back_of_gap _ _ 224 (by rw [h2]; exact lt_usize _ (by decide))

theorem callMem2_pre_read96 (sel : UInt256) (I : ExecutionEnv) (M : ByteArray) (hM : M.size = 256) :
    ((callerWord I).toByteArray.write 0 (sel.toByteArray.write 0 M 160 32) 192 32).readWithPadding 96 32 =
      M.readWithPadding 96 32 := by
  obtain ⟨h1, -, -⟩ := callMem2_sizes sel I ⟨0⟩ M hM
  rw [write32_read_below _ _ 192 96 (by rw [toByteArray_size]) (by rw [h1] <;> omega) (by decide),
    write32_read_below _ _ 160 96 (by rw [toByteArray_size]) (by rw [hM] <;> omega) (by decide)]

theorem callMem2_read96 (sel : UInt256) (I : ExecutionEnv) (v : UInt256) (M : ByteArray) (hM : M.size = 256) :
    (callMem2 sel I v M).readWithPadding 96 32 = M.readWithPadding 96 32 := by
  obtain ⟨-, h2, -⟩ := callMem2_sizes sel I v M hM
  rw [write32_read_below _ _ 224 96 (by rw [toByteArray_size]) (by rw [h2] <;> omega) (by decide),
    callMem2_pre_read96 sel I M hM]

end Tests.Pipeline.VyperWrapper
