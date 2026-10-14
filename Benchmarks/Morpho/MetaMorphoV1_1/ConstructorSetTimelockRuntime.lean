import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorTimelockGuard
import Benchmarks.Morpho.MetaMorphoV1_1.SetTimelockSource

/-! Store the initial timelock, emit its event, clear pending timelock, and read the vault name. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory metaMorphoV1_1CreationBlocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

def constructorVaultNameTail (a : ConstructorArgs) : List UInt256 :=
  [UInt256.ofNat a.name.size, UInt256.ofNat a.argumentEnd, UInt256.ofNat a.nameEnd,
    UInt256.ofNat a.asset.val, UInt256.ofNat a.morpho.val, ⟨32⟩, ⟨64⟩]

def constructorSetTimelockAccounts (I : ExecutionEnv) (σ : AccountMap) (value : UInt256) : AccountMap :=
  sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨14⟩ value) ⟨17⟩ ⟨0⟩

theorem constructorSetTimelockRuntime {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (ptr : UInt256) (hperm : I.perm = true)
    (hname : BytesBuffer mem (UInt256.ofNat a.argumentEnd) a.name)
    (hsmall : a.name.size < 2 ^ 64)
    (hbelow : (UInt256.ofNat a.argumentEnd).toNat + 32 + a.name.size ≤ ptr.toNat)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨716⟩
      (constructorTimelockTail a ptr) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 ⟨780⟩
      (constructorVaultNameTail a) (writeWord mem ptr.toNat a.initialTimelock) aw' rdata
      (constructorSetTimelockAccounts I σ a.initialTimelock) k' C' := by
  have hl := (hname.writeWord ptr.toNat a.initialTimelock (.inl hbelow)).length
  simp only [Reasoning.Theory.writeWord] at hl
  have hn : (UInt256.ofNat a.name.size).toNat = a.name.size :=
    UInt256.toNat_ofNat_of_lt (by change a.name.size < 2 ^ 256; omega)
  obtain ⟨aw1, k1, C1, r1⟩ := metaMorphoV1_1Creation_block_716_fallthrough_packed (by simp) hperm
    (by rw [hl]; apply ugt_zero; rw [hn]; change a.name.size ≤ 2 ^ 64 - 1; omega) rd
  refine ⟨aw1, k1, C1, ?_⟩
  simpa only [metaMorphoV1_1Creation_block_716_fallthrough_stack,
    metaMorphoV1_1Creation_block_716_fallthrough_memory, hl,
    constructorVaultNameTail, constructorSetTimelockAccounts, Reasoning.Theory.writeWord] using r1

theorem SourceState.constructorSetTimelock {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (value : UInt256) :
    SourceState s0 I (constructorSetTimelockAccounts I σ value) (setTimelockState evm value) := by
  have h1 := hs.readModifyWrite ⟨14⟩ (fun _ ↦ value)
  have h2 := h1.readModifyWrite ⟨17⟩ (fun _ ↦ ⟨0⟩)
  exact h2

end Benchmarks.Morpho.MetaMorphoV1_1
