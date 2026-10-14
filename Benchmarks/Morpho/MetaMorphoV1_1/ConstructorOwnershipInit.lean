import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorOwnershipRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorOwnershipSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorDomainContext

/-! Source/bytecode continuation after transferring ownership during construction. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

theorem constructorOwnershipInit {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (ok : Bool) (out : ByteArray)
    (hs : SourceState s0 I σ evm) (hperm : I.perm = true)
    (hlo : 96 ≤ (constructorDecimalsCursor a out).toNat)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨616⟩
      (constructorOwnershipTail a) (constructorDomainReadyMemory mem a ok out I) aw rdata σ k C) :
    (ExecBlock config (constructorDomainReadyFrame a ok out I) evm
        (contract.ctor.body.drop 25) .reverted ∧
      RDrev (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) g s0) ∨
    (a.morpho ≠ ⟨0, by decide⟩ ∧
      (∀ result, ExecBlock config (constructorOwnershipFrame (constructorDomainReadyFrame a ok out I))
          (ownershipState evm (UInt256.ofNat a.owner.val)) (contract.ctor.body.drop 27) result →
        ExecBlock config (constructorDomainReadyFrame a ok out I) evm
          (contract.ctor.body.drop 25) result) ∧
      SourceState s0 I (ownershipAccounts I σ (UInt256.ofNat a.owner.val))
        (ownershipState evm (UInt256.ofNat a.owner.val)) ∧
      ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨711⟩
        (constructorTimelockTail a (UInt256.ofNat ((constructorDecimalsCursor a out).toNat + 192)))
        (constructorDomainReadyMemory mem a ok out I) aw' rdata
        (ownershipAccounts I σ (UInt256.ofNat a.owner.val)) k' C') := by
  have hf := constructorDomainCachedMemory_free (constructorAssetReadyMemory mem a ok out) I
    (constructorDecimalsCursor a out).toNat hlo
  have hc := constructorDomainReadyFrame_contract a ok out I
  have ho := constructorDomainReadyFrame_owner a ok out I
  have hm := constructorDomainReadyFrame_morpho a ok out I
  rcases constructorOwnershipRuntime a
    (UInt256.ofNat ((constructorDecimalsCursor a out).toNat + 192)) hperm hf rd with hfail | hnext
  · exact .inl ⟨constructorOwnershipReverts hc ho hm hfail.1, hfail.2⟩
  · refine .inr ⟨hnext.1, ?_, SourceState.constructorOwnership hs a.owner, hnext.2⟩
    intro result htail
    exact constructorOwnershipPrefix hc ho hm hnext.1 htail

end Benchmarks.Morpho.MetaMorphoV1_1
