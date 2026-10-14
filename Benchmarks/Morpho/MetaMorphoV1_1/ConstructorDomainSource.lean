import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorShortLiteral
import Benchmarks.Morpho.MetaMorphoV1_1.PackedSource

/-! The fixed EIP-712 name, version, hashes, and chain identifier assigned by construction. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def constructorNameHash : UInt256 := uInt256OfByteArray (KEC ByteArray.empty)
def constructorVersionHash : UInt256 := uInt256OfByteArray (KEC "1".toUTF8)

def constructorDomainConstantsFrame (frame : Frame) : Frame :=
  { frame with
    immutables :=
      ((((frame.immutables.insert "_name" (uint256Value ⟨0⟩)).insert
        "_version" (uint256Value constructorVersionWord)).insert
        "_hashedName" (uint256Value constructorNameHash)).insert
        "_hashedVersion" (uint256Value constructorVersionHash)).insert
        "_cachedChainId" (uint256Value (UInt256.ofNat Ethereum.chainId)) }

def constructorDomainConstantsBody : List Stmt :=
  [.setImmutable "_name" (.intLit 0),
   .setImmutable "_version" (.intLit 0x3100000000000000000000000000000000000000000000000000000000000001),
   .setImmutable "_hashedName"
     (.cast (.keccak256 (.bytesLit ByteArray.empty)) (.elem (.int (.uint ⟨256, by decide⟩)))),
   .setImmutable "_hashedVersion"
     (.cast (.keccak256 (.bytesLit "1".toUTF8)) (.elem (.int (.uint ⟨256, by decide⟩)))),
   .setImmutable "_cachedChainId" (.env .chainid)]

-- LIBRARY CANDIDATE: every EVM word fits an unsigned 256-bit immutable declaration.
theorem uint256Value_fits (word : UInt256) :
    elemValueFits (.int (.uint ⟨256, by decide⟩)) (uint256Value word) = true := by
  simp only [elemValueFits, decide_eq_true_eq]
  exact ⟨Int.natCast_nonneg _, Int.ofNat_lt.mpr word.val.isLt⟩

theorem constructorDomainConstantsSource {frame : Frame} {evm : State}
    (hcontract : frame.contract = contract) :
    ExecBlock config frame evm constructorDomainConstantsBody
      (.ok (constructorDomainConstantsFrame frame) evm) := by
  apply ExecBlock.consNormal (ExecStmt.setImmutable (value := uint256Value ⟨0⟩)
    (ty := .int (.uint ⟨256, by decide⟩)) ?_ ?_ (uint256Value_fits _))
  · apply ExecBlock.consNormal (ExecStmt.setImmutable (value := uint256Value constructorVersionWord)
      (ty := .int (.uint ⟨256, by decide⟩)) ?_ ?_ (uint256Value_fits _))
    · apply ExecBlock.consNormal (ExecStmt.setImmutable (value := uint256Value constructorNameHash)
        (ty := .int (.uint ⟨256, by decide⟩)) ?_ ?_ (uint256Value_fits _))
      · apply ExecBlock.consNormal (ExecStmt.setImmutable (value := uint256Value constructorVersionHash)
          (ty := .int (.uint ⟨256, by decide⟩)) ?_ ?_ (uint256Value_fits _))
        · apply ExecBlock.consNormal (ExecStmt.setImmutable
            (value := uint256Value (UInt256.ofNat Ethereum.chainId))
            (ty := .int (.uint ⟨256, by decide⟩)) ?_ ?_ (uint256Value_fits _)) ExecBlock.nil
          · simp only [evalExpr?, pure]
            rfl
          · change immutableType? frame.contract "_cachedChainId" = _
            rw [hcontract]
            rfl
        · exact evalExpr_bytes32ToUint (evalExpr_keccakWord (by simp only [evalExpr?, pure]))
        · change immutableType? frame.contract "_hashedVersion" = _
          rw [hcontract]
          rfl
      · exact evalExpr_bytes32ToUint (evalExpr_keccakWord (by simp only [evalExpr?, pure]))
      · change immutableType? frame.contract "_hashedName" = _
        rw [hcontract]
        rfl
    · simp only [evalExpr?, pure]
      rfl
    · change immutableType? frame.contract "_version" = _
      rw [hcontract]
      rfl
  · simp only [evalExpr?, pure]
    rfl
  · rw [hcontract]
    rfl

end Benchmarks.Morpho.MetaMorphoV1_1
