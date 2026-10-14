import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStorageMemory
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStorageSource

/-! Both initial ERC20 metadata assignments, with their source and memory continuations. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option autoImplicit false

def constructorMetadataState (evm : State) : State :=
  storageStringWriteState (storageStringWriteState evm ⟨3⟩ ByteArray.empty) ⟨4⟩ ByteArray.empty

theorem storageStringWrite_sourceState {s0 evm : State} {I : ExecutionEnv} {σ : AccountMap}
    (hs : SourceState s0 I σ evm) (slot : UInt256) (bytes : ByteArray) :
    SourceState s0 I (storageStringWriteState evm slot bytes).accountMap
      (storageStringWriteState evm slot bytes) :=
  ⟨(storageStringWriteState_world evm slot bytes).trans hs.world,
    (storageStringWriteState_env evm slot bytes).trans hs.env, rfl⟩

theorem constructorStorageInit {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    (a : ConstructorArgs) (hs : SourceState s0 I σ evm) (hperm : I.perm = true)
    (hlo : 96 ≤ a.stringsEnd) (hptr : a.stringsEnd + 160 < UInt256.size)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨229⟩
      [UInt256.ofNat (a.stringsEnd + 32), UInt256.ofNat (a.stringsEnd + 64),
        UInt256.ofNat a.stringsEnd, UInt256.ofNat (a.stringsEnd + 96), UInt256.ofNat a.owner.val,
        UInt256.ofNat a.morpho.val, UInt256.ofNat a.argumentEnd, UInt256.ofNat a.nameEnd,
        UInt256.ofNat a.asset.val, a.initialTimelock, ⟨32⟩, ⟨64⟩]
      (constructorLiteralMemory mem a.stringsEnd) aw rdata σ k C) :
    (ExecBlock config (constructorReadyFrame a) evm (contract.ctor.body.drop 8) .reverted ∧
      RDrev (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) g s0) ∨
    (∃ mem' aw' k' C',
      (∀ result, ExecBlock config (constructorReadyFrame a) (constructorMetadataState evm)
          (contract.ctor.body.drop 10) result →
        ExecBlock config (constructorReadyFrame a) evm (contract.ctor.body.drop 8) result) ∧
      SourceState s0 I (constructorMetadataState evm).accountMap (constructorMetadataState evm) ∧
      (∀ limit, ByteMemoryPrefix (constructorVersionMemory mem a.stringsEnd) mem' limit) ∧
      memLoad ⟨64⟩ mem' = UInt256.ofNat (a.stringsEnd + 160) ∧
      RD (metaMorphoV1_1CreationBytecode ++ a.encoded.toByteArray) I g s0 ⟨434⟩
        (constructorMetadataTail a a.stringsEnd true) mem' aw' rdata
        (constructorMetadataState evm).accountMap k' C') := by
  obtain ⟨_, _, _, r1⟩ := constructorVersionEntry a a.stringsEnd hlo hptr rd
  obtain ⟨_, _, _, r2⟩ := constructorMetadataHeader false (by simp [constructorMetadataTail]) r1
  have hh3 : storageStringHeader evm ⟨3⟩ = solcSlotWord σ I ⟨3⟩ := hs.storageRead _
  by_cases hv3 : storageStringValid (storageStringHeader evm ⟨3⟩)
  · have hsource3 := constructorMetadataAssign a
      [UInt256.ofNat (a.stringsEnd + 160), UInt256.ofNat (a.stringsEnd + 96),
        UInt256.ofNat (a.stringsEnd + 64), UInt256.ofNat (a.stringsEnd + 32),
        UInt256.ofNat a.stringsEnd, UInt256.ofNat a.nameEnd, UInt256.ofNat a.argumentEnd]
      false evm hv3
    obtain ⟨_, _, _, r3⟩ := constructorMetadataValid a a.stringsEnd false (hh3 ▸ hv3) r2
    obtain ⟨mem1, _, _, _, hm1, r4⟩ := constructorInitializeMetadata a a.stringsEnd false hs hperm hv3 r3
    have hsize : 96 ≤ (constructorVersionMemory mem a.stringsEnd).size := by
      simp only [constructorVersionMemory, writeWord_sparse_size]; omega
    obtain ⟨hp1, hf1⟩ := constructorStorageMemoryPreserved false hsize hm1
    have hb := constructorVersionMemory_empty mem a.stringsEnd ⟨2, by decide⟩ hlo hptr
    have hb1 := hb.preserve (hp1 (constructorVersionMemory mem a.stringsEnd).size)
      (by rw [UInt256.toNat_ofNat_of_lt (show a.stringsEnd + 32 * 2 < UInt256.size by omega)]; omega)
      hb.size
    obtain ⟨_, _, _, r5⟩ := constructorSymbolEntry a a.stringsEnd hb1.length r4
    obtain ⟨_, _, _, r6⟩ := constructorMetadataHeader true (by simp [constructorMetadataTail]) r5
    let evm1 := storageStringWriteState evm ⟨3⟩ ByteArray.empty
    have hs1 := storageStringWrite_sourceState hs ⟨3⟩ ByteArray.empty
    have hh4 : storageStringHeader evm1 ⟨4⟩ = solcSlotWord evm1.accountMap I ⟨4⟩ := hs1.storageRead _
    by_cases hv4 : storageStringValid (storageStringHeader evm1 ⟨4⟩)
    · obtain ⟨_, _, _, r7⟩ := constructorMetadataValid a a.stringsEnd true (hh4 ▸ hv4) r6
      obtain ⟨mem2, aw8, k8, C8, hm2, r8⟩ := constructorInitializeMetadata a a.stringsEnd true hs1 hperm hv4 r7
      obtain ⟨hp2, hf2⟩ := constructorStorageMemoryPreserved true
        (le_trans hsize (hp1 0).size) hm2
      refine .inr ⟨mem2, aw8, k8, C8, ?_, storageStringWrite_sourceState hs1 ⟨4⟩ ByteArray.empty,
        fun limit => (hp1 limit).trans (hp2 limit), ?_, r8⟩
      · intro result hrest
        exact ExecBlock.consNormal hsource3
          (ExecBlock.consNormal (constructorMetadataAssign a _ true evm1 hv4) hrest)
      · exact hf2.trans (hf1.trans (constructorVersionMemory_free mem a.stringsEnd))
    · refine .inl ⟨?_, constructorMetadataInvalid a a.stringsEnd true (hh4 ▸ hv4) r6⟩
      exact ExecBlock.consNormal hsource3
        (ExecBlock.consRevert (constructorMetadataAssignRevert a _ true evm1 hv4))
  · refine .inl ⟨?_, constructorMetadataInvalid a a.stringsEnd false (hh3 ▸ hv3) r2⟩
    exact ExecBlock.consRevert (constructorMetadataAssignRevert a _ false evm hv3)

end Benchmarks.Morpho.MetaMorphoV1_1
