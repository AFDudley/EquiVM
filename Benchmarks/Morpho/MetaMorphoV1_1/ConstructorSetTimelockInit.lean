import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorSetTimelockRuntime
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorSetTimelockSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultBuffers

/-! Initial timelock setup, retaining both metadata buffers for their storage writers. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

def constructorTimelockMemory (mem : ByteArray) (a : ConstructorArgs) (ok : Bool)
    (out : ByteArray) (I : ExecutionEnv) : ByteArray :=
  writeWord (constructorDomainReadyMemory mem a ok out I)
    ((constructorDecimalsCursor a out).toNat + 192) a.initialTimelock

theorem constructorSetTimelockInit {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (ok : Bool) (out : ByteArray) (hs : SourceState s0 I σ evm)
    (hperm : I.perm = true) (hbound : 23666 + a.encoded.length < UInt256.size)
    (hsmall : a.argumentEnd < 2 ^ 64) (hname : a.nameEnd < 2 ^ 64)
    (hcursorLo : a.stringsEnd ≤ (constructorDecimalsCursor a out).toNat)
    (hcursorFit : (constructorDecimalsCursor a out).toNat + 192 < 2 ^ 64)
    (hp : ByteMemoryPrefix (constructorVersionMemory (constructorStringsMemory a) a.stringsEnd)
      mem (a.stringsEnd + 160))
    (rd : RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨716⟩
      (constructorTimelockTail a (UInt256.ofNat ((constructorDecimalsCursor a out).toNat + 192)))
      (constructorDomainReadyMemory mem a ok out I) aw rdata σ k C) :
    (∀ result, ExecBlock config (constructorTimelockReadyFrame a ok out I)
        (setTimelockState evm a.initialTimelock) (contract.ctor.body.drop 29) result →
      ExecBlock config (constructorTimelockCheckedFrame
        (constructorOwnershipFrame (constructorDomainReadyFrame a ok out I)) a.initialTimelock)
        evm (contract.ctor.body.drop 28) result) ∧
    SourceState s0 I (constructorSetTimelockAccounts I σ a.initialTimelock)
      (setTimelockState evm a.initialTimelock) ∧
    BytesBuffer (constructorTimelockMemory mem a ok out I) (UInt256.ofNat a.argumentEnd) a.name ∧
    BytesBuffer (constructorTimelockMemory mem a ok out I) (UInt256.ofNat a.nameEnd) a.symbol ∧
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨780⟩
      (constructorVaultNameTail a) (constructorTimelockMemory mem a ok out I) aw' rdata
      (constructorSetTimelockAccounts I σ a.initialTimelock) k' C' := by
  obtain ⟨hn, hv⟩ := constructorDomainReadyMemory_buffers mem a ok out I hbound hsmall hname hcursorLo hp
  have hf : (UInt256.ofNat ((constructorDecimalsCursor a out).toNat + 192)).toNat =
      (constructorDecimalsCursor a out).toNat + 192 :=
    UInt256.toNat_ofNat_of_lt (by change _ < 2 ^ 256; omega)
  have hnlo : (UInt256.ofNat a.argumentEnd).toNat + 32 + a.name.size ≤
      (constructorDecimalsCursor a out).toNat + 192 := by
    rw [UInt256.toNat_ofNat_of_lt (by change a.argumentEnd < 2 ^ 256; omega)]
    have hpad : a.name.size ≤ paddedSize a.name.size := by unfold paddedSize; omega
    unfold ConstructorArgs.stringsEnd ConstructorArgs.nameEnd at hcursorLo
    omega
  have hvlo : (UInt256.ofNat a.nameEnd).toNat + 32 + a.symbol.size ≤
      (constructorDecimalsCursor a out).toNat + 192 := by
    rw [UInt256.toNat_ofNat_of_lt (by change a.nameEnd < 2 ^ 256; omega)]
    have hpad : a.symbol.size ≤ paddedSize a.symbol.size := by unfold paddedSize; omega
    unfold ConstructorArgs.stringsEnd at hcursorLo
    omega
  obtain ⟨aw1, k1, C1, r1⟩ := constructorSetTimelockRuntime a
    (UInt256.ofNat ((constructorDecimalsCursor a out).toNat + 192)) hperm hn
    (a.string_sizes_small hsmall).1 (by rw [hf]; exact hnlo) rd
  refine ⟨?_, SourceState.constructorSetTimelock hs a.initialTimelock,
    hn.writeWord _ _ (.inl hnlo), hv.writeWord _ _ (.inl hvlo), aw1, k1, C1, ?_⟩
  · intro result htail
    apply constructorSetTimelockPrefix
    · exact constructorTimelockCheckedFrame_contract a.initialTimelock
        (constructorDomainReadyFrame_contract a ok out I)
    · apply constructorTimelockCheckedFrame_value
      rw [constructorOwnershipFrame, store_get_ne _ _ (by decide)]
      exact constructorDomainReadyFrame_timelock a ok out I
    · exact htail
  · simpa only [hf, constructorTimelockMemory] using r1

end Benchmarks.Morpho.MetaMorphoV1_1
