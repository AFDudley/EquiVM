import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStrictDecimalsABI
import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSource
import Benchmarks.EAS.Attester.LocalArray

/-! Source execution for strict decimals decoding and its checked return reservation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def constructorStrictDecimalsBody : List Stmt :=
  [.externalCall (.var "assetAddress") "decimals" (.intLit 0) [] "assetDecimals" false,
   reserveBytes 32]

def constructorStrictDecimalsFrame (frame : Frame) (ptr : UInt256) (out : ByteArray) : Frame :=
  { frame with locals := (frame.locals.insert "assetDecimals"
      (uint256Value (calldataWord out 0))).insert cursorName (uint256Value (nextCursor ptr ⟨32⟩)) }

theorem constructorStrictDecimalsBodySplit : contract.ctor.body.drop 34 =
    constructorStrictDecimalsBody ++ contract.ctor.body.drop 36 := rfl

theorem constructorStrictDecimalsSuccess {frame : Frame} {evm evm' : State}
    {asset : AccountAddress} {ptr : UInt256} {out : ByteArray}
    (hc : frame.contract = contract)
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (ha : frame.locals.get? "assetAddress" = some (.address asset))
    (hcall : typedCallViaEVM config evm asset "decimals" 0 [] (true, evm', out) false)
    (hout : out.size < 2 ^ 255)
    (hvalid : 32 ≤ out.size ∧ (calldataWord out 0).toNat < 256 ∧ allocationFits ptr ⟨32⟩) :
    ExecBlock config frame evm constructorStrictDecimalsBody
      (.ok (constructorStrictDecimalsFrame frame ptr out) evm') := by
  have htgt : EVM.address (asset : Nat) = asset := evm_address_of_address_toNat asset
  refine ExecBlock.consNormal (ExecStmt.externalCallSuccess (sendVal := 0) (evalLocalValue ha)
    (by simp only [evalExpr?, pure]) (by rfl) (by rw [htgt]; exact hcall)
    (by rw [constructorStrictDecimalsDecode hout, if_pos ⟨hvalid.1, hvalid.2.1⟩])) ?_
  refine ExecBlock.consNormal (allocateCallReturns cursorName
    (by change lookupCallable? frame.contract _ = _; rw [hc]; exact allocateFunction_lookup)
    (show evalExpr? config
      { frame with locals := frame.locals.insert "assetDecimals" (uint256Value (calldataWord out 0)) }
      evm' (.var cursorName) = .ok (uint256Value ptr) from
        evalLocalValue (by rw [store_get_ne _ _ (by decide)]; exact hp))
    (by simp only [evalExpr?, pure]; rfl) hvalid.2.2) ExecBlock.nil

theorem constructorStrictDecimalsRevert {frame : Frame} {evm evm' : State}
    {asset : AccountAddress} {ptr : UInt256} {out : ByteArray} {ok : Bool}
    (hc : frame.contract = contract)
    (hp : frame.locals.get? cursorName = some (uint256Value ptr))
    (ha : frame.locals.get? "assetAddress" = some (.address asset))
    (hcall : typedCallViaEVM config evm asset "decimals" 0 [] (ok, evm', out) false)
    (hout : out.size < 2 ^ 255)
    (hbad : ¬ (ok = true ∧ 32 ≤ out.size ∧
      (calldataWord out 0).toNat < 256 ∧ allocationFits ptr ⟨32⟩)) :
    ExecBlock config frame evm constructorStrictDecimalsBody .reverted := by
  have htgt : EVM.address (asset : Nat) = asset := evm_address_of_address_toNat asset
  cases ok with
  | false =>
      exact ExecBlock.consRevert (ExecStmt.externalCallFailure (sendVal := 0) (evalLocalValue ha)
        (by simp only [evalExpr?, pure]) (by rfl) (by rw [htgt]; exact hcall))
  | true =>
      by_cases hd : 32 ≤ out.size ∧ (calldataWord out 0).toNat < 256
      · refine ExecBlock.consNormal (ExecStmt.externalCallSuccess (sendVal := 0) (evalLocalValue ha)
          (by simp only [evalExpr?, pure]) (by rfl) (by rw [htgt]; exact hcall)
          (by rw [constructorStrictDecimalsDecode hout, if_pos hd])) ?_
        apply ExecBlock.consRevert
        exact allocateCallReverts cursorName
          (by change lookupCallable? frame.contract _ = _; rw [hc]; exact allocateFunction_lookup)
          (show evalExpr? config
            { frame with locals := frame.locals.insert "assetDecimals" (uint256Value (calldataWord out 0)) }
            evm' (.var cursorName) = .ok (uint256Value ptr) from
              evalLocalValue (by rw [store_get_ne _ _ (by decide)]; exact hp))
          (by simp only [evalExpr?, pure]; rfl) (fun hf => hbad ⟨rfl, hd.1, hd.2, hf⟩)
      · exact ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert (sendVal := 0)
          (evalLocalValue ha) (by simp only [evalExpr?, pure]) (by rfl)
          (by rw [htgt]; exact hcall) (by rw [constructorStrictDecimalsDecode hout, if_neg hd]))

end Benchmarks.Morpho.MetaMorphoV1_1
