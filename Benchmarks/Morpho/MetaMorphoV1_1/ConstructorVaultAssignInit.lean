import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultWrite
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorVaultSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConstructorStorageInit

/-! Couple the vault metadata writer to its source assignment, including invalid old headers. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1CreationBytecode ConstructorArgs.encoded
set_option autoImplicit false

theorem constructorVaultAssignInit {tail : ByteArray} {I : ExecutionEnv} {g : Sat256}
    {s0 evm : State} {frame : Frame} {mem rdata bytes : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {ptr : UInt256}
    (a : ConstructorArgs) (symbol : Bool) (hs : SourceState s0 I σ evm) (hperm : I.perm = true)
    (hcontract : frame.contract = contract)
    (hget : frame.locals.get? (constructorVaultArgName symbol) = some (.bytes bytes))
    (hbase : frame.locals.get? (stringViewField symbol) = none)
    (buffer : StringBuffer mem ptr.toNat bytes) (hlo : 96 ≤ ptr.toNat)
    (hfit : ptr.toNat + 32 + bytes.size < UInt256.size) (hsmall : bytes.size < 2 ^ 64)
    (rd : RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultHeaderPC symbol)
      (UInt256.ofNat bytes.size :: ptr :: constructorVaultTail a symbol) mem aw rdata σ k C) :
    (ExecBlock config frame evm (contract.ctor.body.drop (if symbol then 31 else 29)) .reverted ∧
      RDrev (metaMorphoV1_1CreationBytecode ++ tail) g s0) ∨
    ((∀ result, ExecBlock config frame (storageStringWriteState evm (stringViewSlot symbol) bytes)
        (contract.ctor.body.drop (if symbol then 32 else 30)) result →
      ExecBlock config frame evm (contract.ctor.body.drop (if symbol then 31 else 29)) result) ∧
      SourceState s0 I (storageStringWriteState evm (stringViewSlot symbol) bytes).accountMap
        (storageStringWriteState evm (stringViewSlot symbol) bytes) ∧
      ∃ mem' aw' k' C', StringBuffer mem' ptr.toNat bytes ∧
        (∀ limit, ByteMemoryPrefix mem mem' limit) ∧
        memLoad ⟨64⟩ mem' = memLoad ⟨64⟩ mem ∧
        RD (metaMorphoV1_1CreationBytecode ++ tail) I g s0 (constructorVaultEncodePC symbol)
          (ptr :: constructorVaultEventPC symbol :: stringSetTopic symbol :: constructorVaultTail a symbol)
          mem' aw' rdata (storageStringWriteState evm (stringViewSlot symbol) bytes).accountMap k' C') := by
  obtain ⟨_, _, _, r1⟩ := constructorVaultHeader symbol
    (by cases symbol <;> simp [constructorVaultTail]) rd
  have hh : storageStringHeader evm (stringViewSlot symbol) =
      solcSlotWord σ I (stringViewSlot symbol) := hs.storageRead _
  rcases constructorVaultCheck a symbol r1 with ⟨hbad, hrev⟩ | ⟨hvalid, _, _, _, r2⟩
  · refine .inl ⟨?_, hrev⟩
    rw [constructorVaultAssignBodySplit]
    exact ExecBlock.consRevert (constructorVaultAssignRevert symbol hcontract hget hbase
      (by rwa [hh]))
  · have hv : storageStringValid (storageStringHeader evm (stringViewSlot symbol)) := by
      rwa [hh]
    refine .inr ⟨?_, storageStringWrite_sourceState hs _ bytes, ?_⟩
    · intro result hrest
      rw [constructorVaultAssignBodySplit]
      exact ExecBlock.consNormal (constructorVaultAssign symbol hcontract hget hbase hv) hrest
    · rw [← hh] at r2
      exact constructorVaultWrite a symbol hs hperm hv buffer hlo hfit hsmall r2

end Benchmarks.Morpho.MetaMorphoV1_1
