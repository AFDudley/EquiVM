import Benchmarks.Morpho.MetaMorphoV1_1.ReallocateArithmeticSource
import Benchmarks.Morpho.MetaMorphoV1_1.StrictPairCallSource
import Benchmarks.Morpho.MetaMorphoV1_1.MorphoWithdrawABI
import Benchmarks.Morpho.MetaMorphoV1_1.MorphoSupplyABI

/-! The strict external calls made by the reallocation branches. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem reallocateWithdrawCallArgs {frame : Frame} {evm : State} {row : ByteArray} {amount shares : UInt256}
    (hr : frame.locals.get? "allocation" = some (reallocateAllocationValue row))
    (hw : frame.locals.get? "withdrawn" = some (uint256Value amount))
    (hs : frame.locals.get? "shares" = some (uint256Value shares)) :
    evalExprs? config frame evm
      [.field (.var "allocation") "marketParams", .var "withdrawn", .var "shares", .env .this, .env .this] =
      .ok [(marketParamsData row).value, uint256Value amount, uint256Value shares,
        .address evm.executionEnv.codeOwner, .address evm.executionEnv.codeOwner] := by
  simp only [evalExprs?, reallocateAllocationParams hr, evalExpr?, hw, hs,
    EvalResult.ofOption, envValue, pure, bind, EvalResult.bind]

theorem reallocateSupplyCallArgs {frame : Frame} {evm : State} {row : ByteArray} {amount : UInt256}
    (hr : frame.locals.get? "allocation" = some (reallocateAllocationValue row))
    (ha : frame.locals.get? "suppliedAssets" = some (uint256Value amount)) :
    evalExprs? config frame evm
      [.field (.var "allocation") "marketParams", .var "suppliedAssets", .intLit 0,
        .env .this, .newBytes (.intLit 0)] =
      .ok [(marketParamsData row).value, uint256Value amount, uint256Value ⟨0⟩,
        .address evm.executionEnv.codeOwner, .bytes ByteArray.empty] := by
  have hn : evalExpr? config frame evm (.newBytes (.intLit 0)) = .ok (.bytes ByteArray.empty) := by
    simp only [evalExpr?, pure, bind, EvalResult.bind]
    rfl
  simp only [evalExprs?, reallocateAllocationParams hr, hn, evalExpr?, ha,
    EvalResult.ofOption, envValue, pure, bind, EvalResult.bind]
  rfl

theorem reallocateWithdrawCallSource {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {values : List Value} {i supplied withdrawn ptr amount shares : UInt256}
    {evm evm' : State} {row out : ByteArray}
    (hl : ReallocateLocals v frame values i supplied withdrawn ptr)
    (hr : frame.locals.get? "allocation" = some (reallocateAllocationValue row))
    (hw : frame.locals.get? "withdrawn" = some (uint256Value amount))
    (hs : frame.locals.get? "shares" = some (uint256Value shares))
    (hcall : typedCallViaEVM config evm v.MORPHO "withdraw" 0
      [(marketParamsData row).value, uint256Value amount, uint256Value shares,
        .address evm.executionEnv.codeOwner, .address evm.executionEnv.codeOwner] (true, evm', out))
    (hhi : out.size < 2 ^ 255) (hlong : 64 ≤ out.size) (hfit : allocationFits ptr ⟨64⟩) :
    ExecBlock config frame evm ((reallocateWithdrawBody.drop 2).take 2)
      (.ok (strictPairCallFrame frame "__c5" ptr out) evm') :=
  strictPairCallSuccess hl.contract hl.cursor (by decide) (evalLocalValue hl.target)
    (reallocateWithdrawCallArgs hr hw hs) hcall (by rw [morphoWithdrawDecode hhi, if_pos hlong]) hfit

theorem reallocateWithdrawCallSourceRevert {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {values : List Value} {i supplied withdrawn ptr amount shares : UInt256}
    {evm evm' : State} {row out : ByteArray} {ok : Bool}
    (hl : ReallocateLocals v frame values i supplied withdrawn ptr)
    (hr : frame.locals.get? "allocation" = some (reallocateAllocationValue row))
    (hw : frame.locals.get? "withdrawn" = some (uint256Value amount))
    (hs : frame.locals.get? "shares" = some (uint256Value shares))
    (hcall : typedCallViaEVM config evm v.MORPHO "withdraw" 0
      [(marketParamsData row).value, uint256Value amount, uint256Value shares,
        .address evm.executionEnv.codeOwner, .address evm.executionEnv.codeOwner] (ok, evm', out))
    (hhi : out.size < 2 ^ 255) (hbad : ok = false ∨ ¬ (64 ≤ out.size ∧ allocationFits ptr ⟨64⟩)) :
    ExecBlock config frame evm ((reallocateWithdrawBody.drop 2).take 2) .reverted :=
  strictPairCallRevert hl.contract hl.cursor (by decide) (evalLocalValue hl.target)
    (reallocateWithdrawCallArgs hr hw hs) hcall (morphoWithdrawDecode hhi) hbad

theorem reallocateSupplyCallSource {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {values : List Value} {i supplied withdrawn ptr amount : UInt256}
    {evm evm' : State} {row out : ByteArray}
    (hl : ReallocateLocals v frame values i supplied withdrawn ptr)
    (hr : frame.locals.get? "allocation" = some (reallocateAllocationValue row))
    (ha : frame.locals.get? "suppliedAssets" = some (uint256Value amount))
    (hcall : typedCallViaEVM config evm v.MORPHO "supply" 0
      [(marketParamsData row).value, uint256Value amount, uint256Value ⟨0⟩,
        .address evm.executionEnv.codeOwner, .bytes ByteArray.empty] (true, evm', out))
    (hhi : out.size < 2 ^ 255) (hlong : 64 ≤ out.size) (hfit : allocationFits ptr ⟨64⟩) :
    ExecBlock config frame evm ((reallocateSupplyBody.drop 6).take 2)
      (.ok (strictPairCallFrame frame "__c9" ptr out) evm') :=
  strictPairCallSuccess hl.contract hl.cursor (by decide) (evalLocalValue hl.target)
    (reallocateSupplyCallArgs hr ha) hcall (by rw [morphoSupplyDecode hhi, if_pos hlong]) hfit

theorem reallocateSupplyCallSourceRevert {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {values : List Value} {i supplied withdrawn ptr amount : UInt256}
    {evm evm' : State} {row out : ByteArray} {ok : Bool}
    (hl : ReallocateLocals v frame values i supplied withdrawn ptr)
    (hr : frame.locals.get? "allocation" = some (reallocateAllocationValue row))
    (ha : frame.locals.get? "suppliedAssets" = some (uint256Value amount))
    (hcall : typedCallViaEVM config evm v.MORPHO "supply" 0
      [(marketParamsData row).value, uint256Value amount, uint256Value ⟨0⟩,
        .address evm.executionEnv.codeOwner, .bytes ByteArray.empty] (ok, evm', out))
    (hhi : out.size < 2 ^ 255) (hbad : ok = false ∨ ¬ (64 ≤ out.size ∧ allocationFits ptr ⟨64⟩)) :
    ExecBlock config frame evm ((reallocateSupplyBody.drop 6).take 2) .reverted :=
  strictPairCallRevert hl.contract hl.cursor (by decide) (evalLocalValue hl.target)
    (reallocateSupplyCallArgs hr ha) hcall (morphoSupplyDecode hhi) hbad

theorem ReallocateLocals.strictPair {v : MetaMorphoV1_1Immutables} {frame : Frame} {values : List Value}
    {i supplied withdrawn cursor : UInt256} (h : ReallocateLocals v frame values i supplied withdrawn cursor)
    (name : Ident) (out : ByteArray) (hn : name ∉ reallocateProtectedLocals) :
    ReallocateLocals v (strictPairCallFrame frame name cursor out) values i supplied withdrawn
      (nextCursor cursor ⟨64⟩) :=
  (h.insert name (strictPairCallValue out) hn).withCursor (nextCursor cursor ⟨64⟩)

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
