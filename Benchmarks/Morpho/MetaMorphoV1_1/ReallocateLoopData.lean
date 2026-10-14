import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateLocals

/-! Calldata bounds and source loop-control facts for reallocation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

def reallocateRowBase (offset i : UInt256) : UInt256 := offset + UInt256.mul i (UInt256.ofNat 192)

def reallocateRemaining (cd : ByteArray) (offset i : UInt256) : UInt256 :=
  UInt256.sub (UInt256.ofNat cd.size) (reallocateRowBase offset i) + UInt256.lnot (UInt256.ofNat 35)

structure ReallocateLoopData (cd : ByteArray) (values : List Value) (offset len : UInt256) : Prop where
  high : cd.size < 2 ^ 255
  extent : offset.toNat + 36 + 192 * len.toNat ≤ cd.size
  count : values.length = len.toNat
  rows : ∀ i : UInt256, i.toNat < len.toNat → values[i.toNat]? = some
    (if MarketParamsChecks (reallocateRowBytes cd ((reallocateRowBase offset i).toNat + 36)) then
      reallocateRowValue (reallocateRowBytes cd ((reallocateRowBase offset i).toNat + 36))
      else ABI.Solc08Calldata.decodeFailure)

theorem reallocateRowBase_toNat {cd : ByteArray} {offset len i : UInt256}
    (hsize : cd.size < 2 ^ 255) (hextent : offset.toNat + 36 + 192 * len.toNat ≤ cd.size)
    (hi : i.toNat < len.toNat) :
    (reallocateRowBase offset i).toNat = offset.toNat + 192 * i.toNat := by
  have hprod : i.toNat * (UInt256.ofNat 192).toNat < UInt256.size := by
    change i.toNat * 192 < 2 ^ 256
    omega
  have hp : (UInt256.mul i (UInt256.ofNat 192)).toNat = i.toNat * (UInt256.ofNat 192).toNat :=
    umul_toNat _ _ hprod
  rw [reallocateRowBase, uadd_toNat, hp]
  change (offset.toNat + i.toNat * 192) % UInt256.size = offset.toNat + 192 * i.toNat
  rw [Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega), Nat.mul_comm i.toNat 192]

set_option maxRecDepth 2000 in
theorem reallocateRemaining_toNat {cd : ByteArray} {offset len i : UInt256}
    (hsize : cd.size < 2 ^ 255) (hextent : offset.toNat + 36 + 192 * len.toNat ≤ cd.size)
    (hi : i.toNat < len.toNat) :
    (reallocateRemaining cd offset i).toNat = cd.size - (reallocateRowBase offset i).toNat - 36 := by
  have hb := reallocateRowBase_toNat hsize hextent hi
  have hmod : cd.size < UInt256.size := lt_trans hsize (by decide)
  have hn : (UInt256.lnot (UInt256.ofNat 35)).toNat = UInt256.size - 36 := rfl
  rw [reallocateRemaining, uadd_toNat, usub_ofNat_word_toNat (by omega) hmod, hn]
  have h36 : 36 ≤ UInt256.size := by decide
  have he : cd.size - (reallocateRowBase offset i).toNat + (UInt256.size - 36) =
      UInt256.size + (cd.size - (reallocateRowBase offset i).toNat - 36) := by omega
  rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

theorem ReallocateLoopData.rowBounds {cd : ByteArray} {values : List Value} {offset len i : UInt256}
    (h : ReallocateLoopData cd values offset len) (hi : i.toNat < len.toNat) :
    (reallocateRowBase offset i).toNat + 228 ≤ cd.size ∧
    192 ≤ (reallocateRemaining cd offset i).toNat ∧
    (reallocateRemaining cd offset i).toNat < 2 ^ 255 := by
  rw [reallocateRemaining_toNat h.high h.extent hi, reallocateRowBase_toNat h.high h.extent hi]
  have he := h.extent
  have hs := h.high
  omega

theorem reallocateConditionSource {v : MetaMorphoV1_1Immutables} {frame : Frame} {evm : State}
    {values : List Value} {i supplied withdrawn ptr : UInt256}
    (h : ReallocateLocals v frame values i supplied withdrawn ptr) :
    evalExpr? config frame evm reallocateCondition = .ok (.bool (decide (i.toNat < values.length))) := by
  rw [reallocateCondition, evalExpr_binary_nonshort (by decide) (by decide)]
  simp only [evalLocalValue h.index, evalLocalArrayLength h.input, bind, EvalResult.bind,
    uint256Value, evalBinaryOp?, Int.ofNat_eq_natCast, Nat.cast_lt]

theorem reallocatePostSource {v : MetaMorphoV1_1Immutables} {frame : Frame} {evm : State}
    {values : List Value} {i supplied withdrawn ptr : UInt256}
    (h : ReallocateLocals v frame values i supplied withdrawn ptr) (hfit : i.toNat + 1 < UInt256.size) :
    ExecBlock config frame evm reallocatePost
      (.ok { frame with locals := frame.locals.insert "i" (uint256Value (i + ⟨1⟩)) } evm) := by
  apply ExecBlock.consNormal (ExecStmt.assign ?_ (assignLocalValue h.index)) ExecBlock.nil
  exact checkedAddSourceOk (evalLocalValue h.index)
    (b := (⟨1⟩ : UInt256)) (by simp only [evalExpr?, pure]; rfl) hfit

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
