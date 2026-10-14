import Benchmarks.CurveVault.TokenMemory

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault

-- LIBRARY CANDIDATE: the single-uint256 typed-call payload.
theorem encodeCallWithSelector_uint256 (selector : ByteArray) (value : UInt256) :
    ABI.encodeCallWithSelector? selector [.elem (.int (.uint ⟨256, by decide⟩))]
      [.int (Int.ofNat value.toNat)] = some (selector ++ value.toByteArray) := by
  rw [ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    show abiTupleHeadSize? [.elem (.int (.uint ⟨256, by decide⟩))] = some 32 from by native_decide]
  simp only [bind, Option.bind, encodeABIValuesFrom?, encodeABIValue_uint256_word,
    show isDynamicABIType (.elem (.int (.uint ⟨256, by decide⟩))) = false from rfl,
    Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  rw [byteArray_toList_toByteArray]

def vyperUint256CallMemory (mem : ByteArray) (off : Nat) (selector value : UInt256) : ByteArray :=
  value.toByteArray.write 0 (selector.toByteArray.write 0 mem off 32) (off + 32) 32

-- LIBRARY CANDIDATE: Vyper's selector suffix followed by one uint256 argument.
theorem vyperUint256CallData (selector value : UInt256) (sel mem : ByteArray) (off : Nat)
    (hsel : selector.toByteArray.extract 28 32 = sel) (hsmall : off + 32 < USize.size) :
    ABI.encodeCallWithSelector? sel [.elem (.int (.uint ⟨256, by decide⟩))]
      [.int (Int.ofNat value.toNat)] =
      some ((vyperUint256CallMemory mem off selector value).readWithPadding (off + 28) 36) := by
  have hgap0 : off - mem.size < USize.size := lt_of_le_of_lt (Nat.sub_le _ _) (by omega)
  have hgap1 : off + 32 - (selector.toByteArray.write 0 mem off 32).size < USize.size :=
    lt_of_le_of_lt (Nat.sub_le _ _) hsmall
  have hs0 := toByteArray_write_size_ge_off_add32 selector mem off hgap0
  have hs1 := toByteArray_write_size_ge_off_add32 value (selector.toByteArray.write 0 mem off 32) (off + 32) hgap1
  have hheader : (vyperUint256CallMemory mem off selector value).readWithPadding (off + 28) 4 = sel := by
    rw [vyperUint256CallMemory,
      toByteArray_write_read_below_len_of_gap_unbounded value _ (off + 32) (off + 28) 4
        (by omega) (by omega) (by omega) hgap1,
      toByteArray_write_read_window_of_gap selector mem off 28 4 (by omega) (by omega) (by omega) hgap0, hsel]
  rw [encodeCallWithSelector_uint256]
  apply congrArg some
  rw [show 36 = 4 + 32 from rfl,
    byteArray_readWithPadding_split_unbounded _ (off + 28) 4 32 (by omega) (by omega) (by exact hs1), hheader]
  rw [show off + 28 + 4 = off + 32 by omega]
  exact congrArg (fun bytes => sel ++ bytes) (toByteArray_write_read_back_of_gap value _ _ hgap1).symm

theorem vyperUint256CallMemory_frame (mem : ByteArray) (off lo hi : Nat) (selector value : UInt256)
    (hsmall : off + 32 < USize.size) (hdisj : hi ≤ off ∨ off + 64 ≤ lo) :
    WordMemoryRange mem (vyperUint256CallMemory mem off selector value) lo hi := by
  exact (wordMemoryRange_write mem selector off lo hi
    (lt_of_le_of_lt (Nat.sub_le _ _) (by omega)) (by rcases hdisj with h | h <;> omega)).trans
    (wordMemoryRange_write _ value (off + 32) lo hi
      (lt_of_le_of_lt (Nat.sub_le _ _) hsmall) (by rcases hdisj with h | h <;> omega))

end Benchmarks.CurveVault
