import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDomainMemory

/-! Evaluate the domain helper while the constructor's immutable store is still partial. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

theorem constructorBuildDomainBody {frame : Frame} (evm : State)
    (hname : frame.immutables.get? "_hashedName" = some (uint256Value constructorNameHash))
    (hversion : frame.immutables.get? "_hashedVersion" = some (uint256Value constructorVersionHash)) :
    ExecFuncBody config frame evm buildDomainFunction.body
      (.returned frame evm (some [wordBytes32Value (constructorDomainHash evm.executionEnv)])) := by
  have ht : evalExpr? config frame evm domainTypeHashExpr =
      .ok (wordBytes32Value domainTypeHash) := by
    simp only [domainTypeHashExpr, evalExpr?, pure]
    native_decide
  have hn : evalExpr? config frame evm (.immutable "_hashedName") =
      .ok (uint256Value constructorNameHash) := by
    simp only [evalExpr?, hname, EvalResult.ofOption]
  have hv : evalExpr? config frame evm (.immutable "_hashedVersion") =
      .ok (uint256Value constructorVersionHash) := by
    simp only [evalExpr?, hversion, EvalResult.ofOption]
  have hc : evalExpr? config frame evm (.env .chainid) =
      .ok (uint256Value (UInt256.ofNat Ethereum.chainId)) := by
    simp only [evalExpr?]
    rfl
  have hs : evalExpr? config frame evm (.env .this) =
      .ok (.address evm.executionEnv.codeOwner) := by
    simp only [evalExpr?]
    rfl
  have hpack := evalExpr_packed (evalPackedArgs_cons ht (encodePacked_bytes32 domainTypeHash)
    (evalPackedArgs_cons (evalExpr_uintToBytes32 hn) (encodePacked_bytes32 constructorNameHash)
      (evalPackedArgs_cons (evalExpr_uintToBytes32 hv) (encodePacked_bytes32 constructorVersionHash)
        (evalPackedArgs_cons hc (encodePacked_uint256 (UInt256.ofNat Ethereum.chainId))
          (evalPackedArgs_cons (args := []) (tail := []) (evalExpr_addressToWord hs)
            (encodePacked_uint256 (UInt256.ofNat evm.executionEnv.codeOwner.val))
            (by simp only [evalPackedArgs?, pure]))))))
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  apply evalExpr_keccakWord
  simpa only [constructorDomainHash, constructorDomainWords, wordBytes, List.toByteArray_append,
    word_toBytesBE_toByteArray_eq_toByteArray, List.append_nil, ByteArray.append_empty] using hpack

theorem constructorBuildDomainCall {frame : Frame} (evm : State) (retVar : Ident)
    (hcontract : frame.contract = contract)
    (hname : frame.immutables.get? "_hashedName" = some (uint256Value constructorNameHash))
    (hversion : frame.immutables.get? "_hashedVersion" = some (uint256Value constructorVersionHash)) :
    ExecStmt config frame evm (.internalCall "_buildDomainSeparator" [] retVar)
      (.ok { frame with
        locals := frame.locals.insert retVar
          (wordBytes32Value (constructorDomainHash evm.executionEnv)) } evm) := by
  exact internalCallFunctionReturn (callee := buildDomainFunction)
    (argVals := []) (value := some [wordBytes32Value (constructorDomainHash evm.executionEnv)])
    (by simp only [evalExprs?, pure]) (by rw [hcontract]; rfl) rfl
    (constructorBuildDomainBody (frame := { frame with locals := ∅ }) evm hname hversion)

theorem constructorDomainConstantsFrame_name (frame : Frame) :
    (constructorDomainConstantsFrame frame).immutables.get? "_hashedName" =
      some (uint256Value constructorNameHash) := by
  rw [constructorDomainConstantsFrame, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem constructorDomainConstantsFrame_version (frame : Frame) :
    (constructorDomainConstantsFrame frame).immutables.get? "_hashedVersion" =
      some (uint256Value constructorVersionHash) := by
  rw [constructorDomainConstantsFrame, store_get_ne _ _ (by decide), store_get_self]

end Benchmarks.Morpho.MetaMorphoV1_1
