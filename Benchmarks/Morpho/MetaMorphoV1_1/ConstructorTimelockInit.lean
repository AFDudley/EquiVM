import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorTimelockSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDomainContext

/-! Couple the optional timelock validation with the constructor continuation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

theorem constructorDomainReadyFrame_timelock (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (I : ExecutionEnv) :
    (constructorDomainReadyFrame a ok out I).locals.get? "initialTimelock" =
      some (uint256Value a.initialTimelock) := by
  rw [constructorDomainReadyFrame_preserves a ok out I "initialTimelock"
    (by decide) (by decide) (by decide) (by decide)]
  apply Std.HashMap.getElem?_ofList_of_mem (k := "initialTimelock") (by decide)
  · simp
  · simp

theorem constructorTimelockInit {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (ok : Bool) (out : ByteArray) (ptr : UInt256)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨711⟩
      (constructorTimelockTail a ptr) mem aw rdata σ k C) :
    (ExecBlock config (constructorOwnershipFrame (constructorDomainReadyFrame a ok out I)) evm
        (contract.ctor.body.drop 27) .reverted ∧
      RDrev (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) g s0) ∨
    (constructorTimelockValid a.initialTimelock ∧
      (∀ result, ExecBlock config (constructorTimelockCheckedFrame
          (constructorOwnershipFrame (constructorDomainReadyFrame a ok out I)) a.initialTimelock)
          evm (contract.ctor.body.drop 28) result →
        ExecBlock config (constructorOwnershipFrame (constructorDomainReadyFrame a ok out I)) evm
          (contract.ctor.body.drop 27) result) ∧
      ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨716⟩
        (constructorTimelockTail a ptr) mem aw' rdata σ k' C') := by
  have hc : (constructorOwnershipFrame (constructorDomainReadyFrame a ok out I)).contract = contract := by
    simpa only [constructorOwnershipFrame] using constructorDomainReadyFrame_contract a ok out I
  have ht : (constructorOwnershipFrame (constructorDomainReadyFrame a ok out I)).locals.get?
      "initialTimelock" = some (uint256Value a.initialTimelock) := by
    rw [constructorOwnershipFrame, store_get_ne _ _ (by decide)]
    exact constructorDomainReadyFrame_timelock a ok out I
  rcases constructorTimelockGuard (by simp) rd with hfail | hnext
  · refine .inl ⟨?_, hfail.2⟩
    rw [constructorTimelockCheckBodySplit]
    exact ExecBlock.consRevert (constructorTimelockCheckReverts hc ht hfail.1)
  · refine .inr ⟨hnext.1, ?_, hnext.2⟩
    intro result htail
    exact constructorTimelockCheckPrefix hc ht hnext.1 htail

end Benchmarks.Morpho.MetaMorphoV1_1
