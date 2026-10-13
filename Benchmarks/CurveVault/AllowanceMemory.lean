import Benchmarks.CurveVault.ApproveInternal
import Benchmarks.CurveVault.AddressWord

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

def vaultAllowanceRawMemory (I : ExecutionEnv) (σ : AccountMap) (mem : ByteArray)
    (ownerOffset allowanceOffset : Nat) : ByteArray :=
  let first := wordAt0Mem ⟨12⟩ (wordAt32Mem (memLoad (UInt256.ofNat ownerOffset) mem) mem)
  let hashed := wordAt0Mem (keccakWord ⟨0⟩ (UInt256.ofNat 64) first)
    (wordAt32Mem (UInt256.ofNat I.source.val) first)
  (codeOwnerStorageWord I σ (keccakWord ⟨0⟩ (UInt256.ofNat 64) hashed)).toByteArray.write 0 hashed allowanceOffset 32

theorem vaultAllowanceRawMemory_eq {I : ExecutionEnv} {σ : AccountMap} {mem : ByteArray}
    {owner old : UInt256} {ownerOffset allowanceOffset : Nat} (hsize : 64 ≤ mem.size)
    (hmo : memLoad (UInt256.ofNat ownerOffset) mem = owner) (hcanon : owner.toNat < EVM.addressModulus)
    (hold : codeOwnerStorageWord I σ (vaultAllowanceSlot (AccountAddress.ofNat owner.toNat) I.source) = old) :
    vaultAllowanceRawMemory I σ mem ownerOffset allowanceOffset =
      old.toByteArray.write 0 (vaultApproveHashMemory mem owner (UInt256.ofNat I.source.val)) allowanceOffset 32 := by
  let first := wordAt0Mem ⟨12⟩ (wordAt32Mem owner mem)
  have hsize0 : first.size = mem.size := vyperHashMem_size _ _ _ hsize
  have hhash0 := vyperHashMem_address ⟨12⟩ owner mem hsize hcanon
  have hhash1 := vyperHashMem_address (vyperMappingSlot ⟨12⟩ (.address (AccountAddress.ofNat owner.toNat)))
    (UInt256.ofNat I.source.val) first (by rw [hsize0]; exact hsize) (addressWord_canonical I.source)
  rw [addressWord_roundtrip] at hhash1
  dsimp only [vaultAllowanceSlot] at hold
  dsimp only [vaultAllowanceRawMemory]
  rw [hmo, hhash0, hhash1, hold]
  rfl

end Benchmarks.CurveVault
