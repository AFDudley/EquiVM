import Benchmarks.Morpho.MetaMorphoV1_1.MaxDepositQueueRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.SupplyMorphoLoopState
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_080

/-! Queue indexing and capacity selection for the mutating supply loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

theorem supplyMorphoQueuePrefix {frame : Frame} {evm s0 : State} {I : ExecutionEnv}
    {σ : AccountMap} {i : UInt256}
    (hcontract : frame.contract = contract) (hqueue : frame.locals.get? "supplyQueue" = none)
    (hconfig : frame.locals.get? "config" = none)
    (hi : frame.locals.get? "i" = some (uint256Value i))
    (hs : SourceState s0 I σ evm) (hbound : i.toNat < (codeOwnerStorageWord I σ ⟨20⟩).toNat) :
    ABlock config evm frame supplyMorphoIteration
      (maxDepositCapFrame frame (maxDepositIdWord I σ i)
        (maxDepositCapWord I σ (maxDepositIdWord I σ i))) (supplyMorphoIteration.drop 2) := by
  constructor
  intro result htail
  have hread := maxDepositQueueRead hcontract hqueue hi
    (by rw [hs.storageRead]; exact hbound)
  rw [hs.storageRead] at hread
  apply ExecBlock.consNormal (ExecStmt.letDecl hread)
  apply ExecBlock.consNormal (ExecStmt.letDecl ?_) htail
  have hcap := maxDepositCapRead (evm := evm) (frame := { frame with
    locals := frame.locals.insert "id" (wordBytes32Value (maxDepositIdWord I σ i)) })
    hcontract (by rw [store_get_ne _ _ (by decide)]; exact hconfig) (store_get_self _ _ _)
  rw [hs.storageRead] at hcap
  exact hcap

theorem maxDepositQueueMemory_prefix (mem : ByteArray) (id : UInt256) (limit : Nat) :
    MemoryPrefix mem (maxDepositQueueMemory mem id) limit := by
  change MemoryPrefix mem (writeWord (writeWord (writeWord mem 0 ⟨20⟩) 0 id) 32 ⟨13⟩) limit
  exact (memoryPrefix_sparse_writeWord _ _ _ _ (.inr (by decide))).trans
    ((memoryPrefix_sparse_writeWord _ _ _ _ (.inr (by decide))).trans
      (memoryPrefix_sparse_writeWord _ _ _ _ (.inr (by decide))))

set_option maxRecDepth 2000 in
theorem supplyMorphoQueueRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {morpho savedMorpho ret i assets : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hbound : i.toNat < (codeOwnerStorageWord I σ ⟨20⟩).toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨17948⟩
      ([i, morpho, assets, savedMorpho, ret] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0
      (if maxDepositCapWord I σ (maxDepositIdWord I σ i) = ⟨0⟩ then ⟨18343⟩ else ⟨17995⟩)
      ([maxDepositCapWord I σ (maxDepositIdWord I σ i), maxDepositIdWord I σ i,
        i, morpho, assets, savedMorpho, ret] ++ R)
      (maxDepositQueueMemory mem (maxDepositIdWord I σ i)) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_17948_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨k2, C2, h2⟩ := supplyQueueIndex v
    (by simp only [List.append, List.length_cons]; omega) hbound
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  have hshift : UInt256.shiftRight
      (codeOwnerStorageWord I σ (maxDepositQueueSlot i))
        (UInt256.shiftLeft ⟨0⟩ (UInt256.ofNat 3)) =
      maxDepositIdWord I σ i := wordShiftRight_zero _
  dsimp only [codeOwnerStorageWord, maxDepositQueueSlot] at hshift
  have hhash : keccakWord ⟨0⟩ ⟨64⟩ (maxDepositQueueMemory mem (maxDepositIdWord I σ i)) =
      solcMappingSlot ⟨13⟩ (maxDepositIdWord I σ i) :=
    twoWordHashMem_solcMappingSlot_any _ _ _
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 184))
      (UInt256.ofNat 1) =
      UInt256.ofNat (2 ^ 184 - 1) := rfl
  by_cases hz : maxDepositCapWord I σ (maxDepositIdWord I σ i) = ⟨0⟩
  · obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_17956_taken_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
      (by rw [hshift]
          change UInt256.isZero (UInt256.land _
            (codeOwnerStorageWord I σ (keccakWord ⟨0⟩ ⟨64⟩
              (maxDepositQueueMemory mem (maxDepositIdWord I σ i))))) ≠ ⟨0⟩
          rw [hhash, hmask, u256_land_comm]
          change UInt256.isZero (maxDepositCapWord I σ (maxDepositIdWord I σ i)) ≠ ⟨0⟩
          rw [hz]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    refine ⟨aw3, k3, C3, ?_⟩
    simp only [metaMorphoV1_1_block_17956_taken_stack,
      metaMorphoV1_1_block_17956_taken_memory, hshift] at h3
    change RD _ _ _ _ _
      (UInt256.land _
        (codeOwnerStorageWord I σ (keccakWord ⟨0⟩ ⟨64⟩
          (maxDepositQueueMemory mem (maxDepositIdWord I σ i)))) :: maxDepositIdWord I σ i :: _) _ _ _ _ _ _ at h3
    rw [hhash, hmask, u256_land_comm] at h3
    simpa only [if_pos hz] using h3
  · obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_17956_fallthrough_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
      (by rw [hshift]
          change UInt256.isZero (UInt256.land _
            (codeOwnerStorageWord I σ (keccakWord ⟨0⟩ ⟨64⟩
              (maxDepositQueueMemory mem (maxDepositIdWord I σ i))))) = ⟨0⟩
          rw [hhash, hmask, u256_land_comm]
          exact isZero_eq_zero_of_ne hz) h2
    refine ⟨aw3, k3, C3, ?_⟩
    simp only [metaMorphoV1_1_block_17956_fallthrough_stack,
      metaMorphoV1_1_block_17956_fallthrough_memory, hshift] at h3
    change RD _ _ _ _ _
      (UInt256.land _
        (codeOwnerStorageWord I σ (keccakWord ⟨0⟩ ⟨64⟩
          (maxDepositQueueMemory mem (maxDepositIdWord I σ i)))) :: maxDepositIdWord I σ i :: _) _ _ _ _ _ _ at h3
    rw [hhash, hmask, u256_land_comm] at h3
    simpa only [if_neg hz] using h3

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
